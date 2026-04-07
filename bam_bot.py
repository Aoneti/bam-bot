import asyncio
import html as html_module
import math
import logging
import os
from dotenv import load_dotenv
load_dotenv()
import uuid
from collections import defaultdict, OrderedDict
from datetime import datetime, timedelta, timezone
from time import time

import aiohttp
import aiosqlite
from aiogram import Bot, Dispatcher, F
from aiogram.types import (
    Message, CallbackQuery,
    ReplyKeyboardMarkup, KeyboardButton,
    InlineKeyboardMarkup, InlineKeyboardButton,
    InlineQuery, InlineQueryResultArticle, InputTextMessageContent,
    ErrorEvent,
)
from aiogram.filters import Command
from aiogram import Router
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from apscheduler.schedulers.asyncio import AsyncIOScheduler

# ================= ЛОГИРОВАНИЕ =================
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(message)s",
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler("bam_bot.log", encoding="utf-8"),
    ]
)
logger = logging.getLogger(__name__)

# ================= НАСТРОЙКИ =================
TOKEN = os.environ.get("BOT_TOKEN", "")
if not TOKEN:
    raise RuntimeError("Переменная окружения BOT_TOKEN не задана!")

EBIRD_API_KEY = os.environ.get("EBIRD_API_KEY", "")  # необязательный, но желательный

API_BASE    = "https://api.inaturalist.org/v1"
EBIRD_BASE  = "https://api.ebird.org/v2"
DB_NAME     = "bam_users.db"

BIRD_ALERT_DAYS       = 90
SCAN_CACHE_TTL        = 240
OBS_CACHE_TTL         = 900
TAXON_CACHE_TTL       = 6 * 3600
HIST_CACHE_TTL        = 24 * 3600
HOTSPOT_CACHE_TTL     = 3600        # 1 час
EBIRD_NOTABLE_TTL     = 1800        # 30 минут
SCHEDULER_BATCH_SIZE  = 20
SCHEDULER_BATCH_DELAY = 0.5
SCAN_COOLDOWN_SEC     = 30
GEOCODE_COOLDOWN_SEC  = 5
API_SEMAPHORE_LIMIT   = 5
AUTO_CHECK_WINDOW_HOURS = 3

RARITY_GLOBAL_COMMON_THRESHOLD  = 10_000
RARITY_LOCAL_RARE_THRESHOLD     = 5
RARITY_LOCAL_UNCOMMON_THRESHOLD = 20

CURRENT_MONTH = datetime.now(timezone.utc).month

bot     = Bot(token=TOKEN)
storage = MemoryStorage()
dp      = Dispatcher(storage=storage)
router  = Router()
dp.include_router(router)

BOT_USERNAME: str          = ""
_api_semaphore: asyncio.Semaphore = None

# ================= FSM =================
class Form(StatesGroup):
    waiting_city          = State()
    waiting_custom_radius = State()

# ================= RATE LIMIT =================
_scan_cooldown:    dict[int, float]   = {}
_fav_cooldown:     dict[tuple, float] = {}
_geocode_cooldown: dict[int, float]   = {}

# ================= КЭШ ВИШЛИСТА =================
_fav_count_cache: dict[int, int] = {}

def _invalidate_fav_count(user_id: int):
    _fav_count_cache.pop(user_id, None)

# ================= ГЛОБАЛЬНЫЕ =================
http_session: aiohttp.ClientSession = None
db_conn:      aiosqlite.Connection  = None

# ================= LRU-КЭШ =================
class LRUCache:
    def __init__(self, max_size: int = 200):
        self._cache: OrderedDict = OrderedDict()
        self._max = max_size

    def get(self, key):
        if key in self._cache:
            self._cache.move_to_end(key)
            return self._cache[key]
        return None

    def set(self, key, value):
        if key in self._cache:
            self._cache.move_to_end(key)
        self._cache[key] = value
        if len(self._cache) > self._max:
            self._cache.popitem(last=False)

_geocode_cache     = LRUCache(max_size=200)
_taxa_search_cache = LRUCache(max_size=100)
_taxon_cache_lru   = LRUCache(max_size=500)
_hist_cache_lru    = LRUCache(max_size=500)
_hotspot_cache     = LRUCache(max_size=200)
_ebird_notable_cache = LRUCache(max_size=200)

# ================= КЭШ СКАНИРОВАНИЯ =================
_scan_cache:       LRUCache             = LRUCache(max_size=1000)
_scan_total_pages: dict[int, dict[int, int]] = {}

def _get_scan_cache(user_id: int, page: int):
    key   = (user_id, page)
    entry = _scan_cache.get(key)
    if entry and (time() - entry[0]) < SCAN_CACHE_TTL:
        return entry[1], entry[2]
    return None, None

def _set_scan_cache(user_id: int, page: int, text: str, species: list, total_pages: int):
    _scan_cache.set((user_id, page), (time(), text, species))
    _scan_total_pages.setdefault(user_id, {})[page] = total_pages

def _get_total_pages_cached(user_id: int, page: int) -> int:
    return (_scan_total_pages.get(user_id) or {}).get(page, 1)

def _invalidate_scan_cache(user_id: int):
    keys_to_delete = [k for k in _scan_cache._cache if k[0] == user_id]
    for k in keys_to_delete:
        del _scan_cache._cache[k]
    _scan_total_pages.pop(user_id, None)

# ================= ОБЩИЙ КЭШ НАБЛЮДЕНИЙ =================
_obs_cache: LRUCache = LRUCache(max_size=500)

def _coord_key(lat: float, lon: float, radius: int, days: int) -> tuple:
    return (round(lat, 2), round(lon, 2), radius, days)

def _get_obs_cache(lat: float, lon: float, radius: int, days: int):
    entry = _obs_cache.get(_coord_key(lat, lon, radius, days))
    if entry and (time() - entry[0]) < OBS_CACHE_TTL:
        return entry[1]
    return None

def _set_obs_cache(lat: float, lon: float, radius: int, days: int, results: list):
    _obs_cache.set(_coord_key(lat, lon, radius, days), (time(), results))

# ================= КЭШ ТАКСОНОВ =================
def _get_taxon_cached(taxon_id: int):
    entry = _taxon_cache_lru.get(taxon_id)
    if entry and (time() - entry[0]) < TAXON_CACHE_TTL:
        return entry[1]
    return None

def _set_taxon_cache(taxon_id: int, data: dict):
    _taxon_cache_lru.set(taxon_id, (time(), data))

# ================= КЭШ ГИСТОГРАММ =================
def _get_hist_cached(taxon_id: int, lat: float, lon: float, radius: int):
    key   = (taxon_id, round(lat, 2), round(lon, 2), radius)
    entry = _hist_cache_lru.get(key)
    if entry and (time() - entry[0]) < HIST_CACHE_TTL:
        return entry[1]
    return None

def _set_hist_cache(taxon_id: int, lat: float, lon: float, radius: int, data: dict):
    _hist_cache_lru.set((taxon_id, round(lat, 2), round(lon, 2), radius), (time(), data))

# ================= ОЧИСТКА =================
def _cleanup_scan_cache():
    now   = time()
    stale = [k for k, v in _scan_cache._cache.items()
             if isinstance(k[1], int) and (now - v[0]) > SCAN_CACHE_TTL]
    for k in stale:
        del _scan_cache._cache[k]
    stale_obs = [k for k, v in _obs_cache._cache.items() if (now - v[0]) > OBS_CACHE_TTL]
    for k in stale_obs:
        del _obs_cache._cache[k]
    logger.debug(f"cache cleanup: scan={len(stale)}, obs={len(stale_obs)}")

def _cleanup_cooldowns():
    threshold = time() - 120
    for k in [k for k, v in _scan_cooldown.items() if v < threshold]:
        del _scan_cooldown[k]
    for k in [k for k, v in _fav_cooldown.items() if v < threshold]:
        del _fav_cooldown[k]

async def _cleanup_rare_notifications():
    try:
        await db_conn.execute(
            "DELETE FROM rare_notifications WHERE notified_at < datetime('now', '-48 hours')"
        )
        await db_conn.commit()
    except Exception:
        logger.error("Ошибка при очистке rare_notifications", exc_info=True)

# ================= БАЗА ДАННЫХ =================
async def init_db():
    async with aiosqlite.connect(DB_NAME) as db:
        await db.execute("PRAGMA journal_mode=WAL")
        await db.execute("""
            CREATE TABLE IF NOT EXISTS users (
                telegram_id    INTEGER PRIMARY KEY,
                lat            REAL,
                lon            REAL,
                radius         INTEGER DEFAULT 10,
                period_days    INTEGER DEFAULT 7,
                alerts_enabled INTEGER DEFAULT 1,
                season_filter  INTEGER DEFAULT 0
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS favorites (
                telegram_id      INTEGER,
                taxon_id         INTEGER,
                taxon_name       TEXT,
                last_notified_at TEXT,
                PRIMARY KEY (telegram_id, taxon_id)
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS species_history (
                telegram_id  INTEGER,
                taxon_id     INTEGER,
                last_seen_at TEXT,
                PRIMARY KEY (telegram_id, taxon_id)
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS rare_notifications (
                telegram_id  INTEGER,
                taxon_id     INTEGER,
                notified_at  TEXT,
                PRIMARY KEY (telegram_id, taxon_id)
            )
        """)
        # Миграции — не падаем если колонка уже есть
        for migration in [
            "ALTER TABLE favorites ADD COLUMN last_notified_at TEXT",
            "ALTER TABLE users ADD COLUMN season_filter INTEGER DEFAULT 0",
        ]:
            try:
                await db.execute(migration)
            except Exception:
                pass
        await db.execute("CREATE INDEX IF NOT EXISTS idx_fav_user     ON favorites(telegram_id)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_users_alerts ON users(alerts_enabled, lat)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_history      ON species_history(telegram_id)")
        await db.commit()

# ================= DB HELPERS =================
async def db_fetch_one(sql: str, params: tuple = ()):
    async with db_conn.execute(sql, params) as cur:
        return await cur.fetchone()

async def db_fetch_all(sql: str, params: tuple = ()):
    async with db_conn.execute(sql, params) as cur:
        return await cur.fetchall()

async def db_exec(sql: str, params: tuple = ()):
    try:
        await db_conn.execute(sql, params)
        await db_conn.commit()
    except Exception:
        await db_conn.rollback()
        raise

# ================= ГЕОКОДИРОВАНИЕ =================
async def geocode_city(query: str):
    key    = query.strip().lower()
    cached = _geocode_cache.get(key)
    if cached:
        return cached
    url     = "https://nominatim.openstreetmap.org/search"
    params  = {"q": query, "format": "json", "limit": 1, "addressdetails": 1}
    headers = {"User-Agent": "BAM-BirdsAroundMeBot/1.0", "Accept-Language": "ru"}
    try:
        async with http_session.get(url, params=params, headers=headers,
                                    timeout=aiohttp.ClientTimeout(total=8)) as r:
            r.raise_for_status()
            data = await r.json()
            if data:
                res    = data[0]
                result = (float(res["lat"]), float(res["lon"]), res.get("display_name", query))
                _geocode_cache.set(key, result)
                return result
    except Exception as ex:
        logger.error(f"Geocoding error: {ex}")
    return None, None, None

async def reverse_geocode(lat: float, lon: float) -> str:
    url     = "https://nominatim.openstreetmap.org/reverse"
    params  = {"lat": lat, "lon": lon, "format": "json", "zoom": 10, "addressdetails": 0}
    headers = {"User-Agent": "BAM-BirdsAroundMeBot/1.0", "Accept-Language": "ru"}
    try:
        async with http_session.get(url, params=params, headers=headers,
                                    timeout=aiohttp.ClientTimeout(total=6)) as r:
            r.raise_for_status()
            data = await r.json()
            return data.get("display_name", f"{lat:.4f}, {lon:.4f}")
    except Exception:
        return f"{lat:.5f}, {lon:.5f}"

# ================= ВСПОМОГАТЕЛЬНЫЕ =================
def haversine(lat1, lon1, lat2, lon2) -> float:
    R    = 6371
    dlat = math.radians(lat2 - lat1)
    dlon = math.radians(lon2 - lon1)
    a    = (math.sin(dlat / 2) ** 2
            + math.cos(math.radians(lat1)) * math.cos(math.radians(lat2)) * math.sin(dlon / 2) ** 2)
    return round(R * 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a)), 1)

def time_ago(dt_str: str) -> str:
    if not dt_str:
        return "недавно"
    try:
        dt = (datetime.fromisoformat(dt_str).replace(tzinfo=timezone.utc)
              if "T" not in dt_str and "+" not in dt_str
              else datetime.fromisoformat(dt_str.replace("Z", "+00:00")))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        delta = datetime.now(timezone.utc) - dt
        if delta.total_seconds() < 0:
            return "недавно"
        if delta.days > 0:
            return f"{delta.days} дн. назад"
        hours = delta.seconds // 3600
        return f"{hours} ч. назад" if hours else "только что"
    except Exception:
        return "недавно"

def days_since(dt_str: str | None) -> int | None:
    if not dt_str:
        return None
    try:
        dt    = datetime.fromisoformat(dt_str.replace("Z", "+00:00"))
        delta = datetime.now(timezone.utc) - dt.astimezone(timezone.utc)
        return delta.days
    except Exception:
        return None

def current_season_name() -> str:
    m = datetime.now(timezone.utc).month
    if m in (3, 4, 5):   return "🌱 весна"
    if m in (6, 7, 8):   return "☀️ лето"
    if m in (9, 10, 11): return "🍂 осень"
    return "❄️ зима"

# ================= БАЗОВЫЙ API-ЗАПРОС =================
async def _raw_api_get(url: str, params: dict) -> dict:
    max_retries = 4
    backoff     = 1.0
    for attempt in range(max_retries):
        async with _api_semaphore:
            try:
                async with http_session.get(
                    url, params=params, timeout=aiohttp.ClientTimeout(total=12)
                ) as r:
                    remaining = r.headers.get("X-RateLimit-Remaining")
                    if remaining is not None:
                        logger.debug(f"iNat rate limit: {remaining} remaining [{url}]")
                    if r.status == 429:
                        ra   = r.headers.get("Retry-After", "")
                        wait = float(ra) if ra.isdigit() else backoff
                        logger.warning(f"429 от iNaturalist — жду {wait}s (попытка {attempt + 1})")
                        await asyncio.sleep(wait)
                        backoff *= 2
                        continue
                    r.raise_for_status()
                    return await r.json()
            except (aiohttp.ClientResponseError, aiohttp.ClientConnectorError,
                    asyncio.TimeoutError) as ex:
                logger.warning(f"API transient error [{url}] попытка {attempt + 1}: {ex}")
                await asyncio.sleep(backoff)
                backoff *= 2
                continue
            except Exception as ex:
                logger.exception(f"Неожиданная ошибка [{url}]: {ex}")
                break
    logger.error(f"API запрос не удался [{url}] после {max_retries} попыток")
    return {}

async def api_get(url: str, params: dict) -> dict:
    return await _raw_api_get(url, params)

# ================= EBIRD API =================
async def _ebird_get(endpoint: str, params: dict) -> list:
    """Запрос к eBird API. Возвращает [] при отсутствии ключа или ошибке."""
    if not EBIRD_API_KEY:
        return []
    url     = f"{EBIRD_BASE}{endpoint}"
    headers = {"X-eBirdApiToken": EBIRD_API_KEY}
    try:
        async with http_session.get(
            url, params=params, headers=headers,
            timeout=aiohttp.ClientTimeout(total=10)
        ) as r:
            if r.status == 429:
                logger.warning("eBird rate limit hit")
                return []
            r.raise_for_status()
            return await r.json()
    except Exception as ex:
        logger.warning(f"eBird API error [{endpoint}]: {ex}")
        return []

async def get_ebird_notable(lat: float, lon: float, dist: int = 25, back: int = 14) -> list:
    """Редкие/необычные наблюдения поблизости по данным eBird (curated reviewers)."""
    key   = (round(lat, 2), round(lon, 2), dist)
    entry = _ebird_notable_cache.get(key)
    if entry and (time() - entry[0]) < EBIRD_NOTABLE_TTL:
        return entry[1]
    results = await _ebird_get("/data/obs/geo/recent/notable", {
        "lat": round(lat, 4), "lng": round(lon, 4),
        "dist": min(dist, 50), "back": min(back, 30),
        "detail": "simple", "hotspot": "false",
    })
    _ebird_notable_cache.set(key, (time(), results))
    return results

async def get_ebird_hotspots(lat: float, lon: float, dist: int = 25) -> list:
    """Ближайшие eBird-хотспоты с числом видов."""
    key   = (round(lat, 2), round(lon, 2), dist)
    entry = _hotspot_cache.get(key)
    if entry and (time() - entry[0]) < HOTSPOT_CACHE_TTL:
        return entry[1]
    results = await _ebird_get("/ref/hotspot/geo", {
        "lat": round(lat, 4), "lng": round(lon, 4),
        "dist": min(dist, 50), "back": 30, "fmt": "json",
    })
    # Сортируем по числу видов (всего за всё время)
    results = sorted(results, key=lambda h: h.get("numSpeciesAllTime", 0), reverse=True)[:10]
    _hotspot_cache.set(key, (time(), results))
    return results

# ================= iNATURALIST API =================
async def get_species_counts(lat, lon, radius, days, page=1, season_filter: bool = False):
    d1   = (datetime.now().date() - timedelta(days=days)).isoformat()
    params = {
        "lat": round(lat, 2), "lng": round(lon, 2), "radius": radius, "d1": d1,
        "iconic_taxa": "Aves", "locale": "ru",
        "per_page": 10, "page": page, "order_by": "observations_count",
    }
    if season_filter:
        params["month"] = datetime.now(timezone.utc).month
    data = await api_get(f"{API_BASE}/observations/species_counts", params)
    return data.get("results", []), data.get("total_results", 0)

async def get_recent_observations(lat, lon, radius, days) -> list:
    cached = _get_obs_cache(lat, lon, radius, days)
    if cached is not None:
        return cached
    d1   = (datetime.now().date() - timedelta(days=days)).isoformat()
    data = await api_get(f"{API_BASE}/observations", {
        "lat": round(lat, 2), "lng": round(lon, 2), "radius": radius, "d1": d1,
        "iconic_taxa": "Aves", "locale": "ru",
        "per_page": 100, "order_by": "observed_on", "order": "desc",
    })
    results = data.get("results", [])
    _set_obs_cache(lat, lon, radius, days, results)
    return results

async def get_latest_observation_for_taxon(lat, lon, radius, days, taxon_id):
    d1   = (datetime.now().date() - timedelta(days=days)).isoformat()
    data = await api_get(f"{API_BASE}/observations", {
        "lat": round(lat, 2), "lng": round(lon, 2), "radius": radius, "d1": d1,
        "taxon_id": taxon_id, "per_page": 1,
        "order_by": "observed_on", "order": "desc", "locale": "ru",
    })
    results = data.get("results", [])
    return results[0] if results else None

async def get_taxon_data(taxon_id: int) -> dict:
    cached = _get_taxon_cached(taxon_id)
    if cached is not None:
        return cached
    data = await api_get(f"{API_BASE}/taxa/{taxon_id}", {"locale": "ru"})
    _set_taxon_cache(taxon_id, data)
    return data

async def get_taxon_name(taxon_id: int) -> str:
    data    = await get_taxon_data(taxon_id)
    results = data.get("results", [])
    if results:
        t = results[0]
        return t.get("preferred_common_name") or t.get("name", str(taxon_id))
    return str(taxon_id)

async def search_taxa_by_name(query: str) -> list:
    key    = query.strip().lower()
    cached = _taxa_search_cache.get(key)
    if cached is not None:
        return cached
    data    = await api_get(f"{API_BASE}/taxa", {
        "q": query, "iconic_taxa": "Aves", "locale": "ru", "per_page": 8,
    })
    results = data.get("results", [])
    _taxa_search_cache.set(key, results)
    return results

async def get_batch_watchlist_observations(lat, lon, radius, days, taxon_ids: list) -> dict:
    if not taxon_ids:
        return {}
    d1   = (datetime.now().date() - timedelta(days=days)).isoformat()
    data = await api_get(f"{API_BASE}/observations", {
        "lat": round(lat, 2), "lng": round(lon, 2), "radius": radius, "d1": d1,
        "taxon_id": ",".join(str(t) for t in taxon_ids),
        "iconic_taxa": "Aves", "locale": "ru",
        "per_page": 200, "quality_grade": "research",
        "order_by": "observed_on", "order": "desc",
    })
    latest: dict = {}
    for obs in data.get("results", []):
        tid = obs["taxon"]["id"]
        if tid not in latest:
            latest[tid] = obs
    return latest

# ================= ОПРЕДЕЛЕНИЕ ПТИЦЫ ПО ФОТО =================
async def identify_bird_photo(photo_bytes: bytes, lat: float = None, lon: float = None) -> list:
    """Отправляет фото в iNaturalist CV API, возвращает топ результатов (только птицы)."""
    try:
        form = aiohttp.FormData()
        form.add_field("file", photo_bytes, filename="photo.jpg", content_type="image/jpeg")
        if lat is not None and lon is not None:
            form.add_field("lat", str(round(lat, 2)))
            form.add_field("lng", str(round(lon, 2)))
        async with _api_semaphore:
            async with http_session.post(
                f"{API_BASE}/computervision/score_image",
                data=form,
                timeout=aiohttp.ClientTimeout(total=30),
            ) as r:
                r.raise_for_status()
                data = await r.json()
        # Фильтруем только птиц (iconic_taxon_name == "Aves" или parent Aves)
        results = []
        for item in data.get("results", []):
            t = item.get("taxon", {})
            if t.get("iconic_taxon_name") == "Aves":
                results.append(item)
            if len(results) >= 5:
                break
        return results
    except Exception as ex:
        logger.error(f"CV API error: {ex}", exc_info=True)
        return []

# ================= ИЗВЛЕЧЕНИЕ ТАКСОНОМИИ И ФЛАГОВ =================
def _extract_taxonomy(taxon_data: dict) -> tuple[str, str]:
    results = taxon_data.get("results", [])
    if not results:
        return "", ""
    family_name = ""
    order_name  = ""
    for ancestor in results[0].get("ancestors", []):
        rank = ancestor.get("rank", "")
        name = ancestor.get("preferred_common_name") or ancestor.get("name", "")
        if rank == "family" and not family_name:
            family_name = name
        elif rank == "order" and not order_name:
            order_name = name
    return family_name, order_name

def _extract_taxon_flags(taxon_data: dict) -> list[str]:
    """Возвращает список значков-флагов: инвазивный, интродуцированный, эндемик."""
    results = taxon_data.get("results", [])
    if not results:
        return []
    t     = results[0]
    flags = []
    if t.get("introduced"):
        flags.append("🌍 Интродуцированный вид")
    if t.get("endemic"):
        flags.append("📌 Эндемик")
    # conservation_status уже используется в редкости — здесь не дублируем
    return flags

# ================= РЕДКОСТЬ И СЕЗОННОСТЬ =================
async def get_rare_and_season(taxon_id: int, lat: float, lon: float, radius: int):
    d1_year = (datetime.now().date() - timedelta(days=365)).isoformat()

    taxon_cached = _get_taxon_cached(taxon_id)
    hist_cached  = _get_hist_cached(taxon_id, lat, lon, radius)

    yearly_task = api_get(f"{API_BASE}/observations/species_counts", {
        "lat": round(lat, 2), "lng": round(lon, 2), "radius": radius, "d1": d1_year,
        "taxon_id": taxon_id, "iconic_taxa": "Aves", "per_page": 1,
    })
    taxon_task = (
        api_get(f"{API_BASE}/taxa/{taxon_id}", {"locale": "ru"})
        if taxon_cached is None else None
    )
    hist_task = (
        api_get(f"{API_BASE}/observations/histogram", {
            "taxon_id": taxon_id,
            "lat": round(lat, 2), "lng": round(lon, 2), "radius": radius,
            "date_field": "observed_on", "interval": "month_of_year",
        })
        if hist_cached is None else None
    )

    gather_tasks   = [t for t in (yearly_task, taxon_task, hist_task) if t is not None]
    gather_results = await asyncio.gather(*gather_tasks)
    result_iter    = iter(gather_results)

    yearly_data = next(result_iter)
    taxon_data  = next(result_iter) if taxon_task  is not None else taxon_cached
    season_data = next(result_iter) if hist_task   is not None else hist_cached

    if taxon_task  is not None: _set_taxon_cache(taxon_id, taxon_data)
    if hist_task   is not None: _set_hist_cache(taxon_id, lat, lon, radius, season_data)

    # --- Редкость ---
    local_count   = 0
    if yearly_data.get("results"):
        local_count = yearly_data["results"][0].get("count", 0)

    is_threatened = False
    global_count  = 0
    if taxon_data and taxon_data.get("results"):
        t             = taxon_data["results"][0]
        cs            = (t.get("conservation_status") or {})
        is_threatened = cs.get("status", "").lower() in ("cr", "en", "vu")
        global_count  = t.get("observations_count", 0)

    if is_threatened:
        rare_emoji, rare_label = "🔴", "охраняемый вид"
    elif global_count > RARITY_GLOBAL_COMMON_THRESHOLD:
        rare_emoji, rare_label = "🟢", "обычная редкость"
    elif local_count <= RARITY_LOCAL_RARE_THRESHOLD:
        rare_emoji, rare_label = "🔴", "редкая в этом районе"
    elif local_count <= RARITY_LOCAL_UNCOMMON_THRESHOLD:
        rare_emoji, rare_label = "🟡", "нечасто встречается"
    else:
        rare_emoji, rare_label = "🟢", "обычная редкость"

    # --- Сезонность ---
    MONTHS      = ["янв","фев","мар","апр","май","июн","июл","авг","сен","окт","ноя","дек"]
    season_text = ""
    raw_hist    = (season_data or {}).get("results") or {}
    if raw_hist:
        hist: dict[str, int] = {}
        for k, v in raw_hist.items():
            hist[k] = int(v.get("count", 0)) if isinstance(v, dict) else (int(v) if v else 0)
        max_c = max(hist.values(), default=0)
        if max_c > 0:
            active = [m for m in range(1, 13) if hist.get(str(m), 0) >= max_c * 0.25]
            if active:
                season_text = ("📅 Встречается круглый год"
                               if len(active) >= 10
                               else "📅 Обычно: " + ", ".join(MONTHS[m - 1] for m in active))

    return rare_emoji, rare_label, season_text, taxon_data

# ================= КООРДИНАТЫ НАБЛЮДЕНИЯ =================
def _parse_obs_coords(obs: dict) -> tuple[float | None, float | None]:
    loc = obs.get("location", "")
    if loc and "," in str(loc):
        try:
            parts = str(loc).split(",")
            return float(parts[0]), float(parts[1])
        except (ValueError, IndexError):
            pass
    raw_lat, raw_lon = obs.get("latitude"), obs.get("longitude")
    if raw_lat is not None and raw_lon is not None:
        try:
            return float(raw_lat), float(raw_lon)
        except (ValueError, TypeError):
            pass
    coords = (obs.get("geojson") or {}).get("coordinates")
    if coords and len(coords) == 2:
        try:
            return float(coords[1]), float(coords[0])
        except (ValueError, TypeError):
            pass
    return None, None

# ================= ФОТО И ЭКРАНИРОВАНИЕ =================
def get_photo_url(obs: dict, size: str = "medium") -> str | None:
    if obs.get("photos"):
        return obs["photos"][0]["url"].replace("square", size)
    return None

def e(text: str) -> str:
    return html_module.escape(str(text))

# ================= КЛАВИАТУРА =================
async def main_keyboard(user_id: int) -> ReplyKeyboardMarkup:
    if user_id not in _fav_count_cache:
        rows = await db_fetch_all(
            "SELECT COUNT(*) FROM favorites WHERE telegram_id = ?", (user_id,)
        )
        _fav_count_cache[user_id] = rows[0][0] if rows else 0
    fav_count = _fav_count_cache[user_id]
    fav_label = f"⭐ Вишлист ({fav_count})" if fav_count else "⭐ Вишлист"
    ebird_ok  = bool(EBIRD_API_KEY)
    kb = [
        [KeyboardButton(text="🐦 Сканировать"), KeyboardButton(text="📷 Определить птицу")],
        [KeyboardButton(text="🚨 Редкие птицы"), KeyboardButton(text=fav_label)],
    ]
    if ebird_ok:
        kb.append([KeyboardButton(text="🗺 Хотспоты рядом"), KeyboardButton(text="⚙️ Настройки")])
    else:
        kb.append([KeyboardButton(text="⚙️ Настройки")])
    return ReplyKeyboardMarkup(keyboard=kb, resize_keyboard=True)

# Временная клавиатура для запроса геолокации из настроек
def _location_request_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[[
            KeyboardButton(text="📍 Отправить геолокацию", request_location=True),
            KeyboardButton(text="❌ Отмена"),
        ]],
        resize_keyboard=True,
        one_time_keyboard=True,
    )

# ================= ГЛОБАЛЬНЫЙ ОБРАБОТЧИК ОШИБОК =================
@router.errors()
async def global_error_handler(event: ErrorEvent):
    logger.error(f"Необработанное исключение: {event.exception}", exc_info=True)
    try:
        update = event.update
        if update.message:
            await update.message.answer("⚠️ Что-то пошло не так. Попробуйте ещё раз.")
        elif update.callback_query:
            await update.callback_query.answer("⚠️ Ошибка. Попробуйте позже.", show_alert=True)
    except Exception:
        pass

# ================= СТАРТ / ОТМЕНА =================
@router.message(Command("start"))
async def start(message: Message, state: FSMContext):
    if not message.from_user:
        return
    await state.clear()
    await db_exec("""
        INSERT OR IGNORE INTO users
        (telegram_id, lat, lon, radius, period_days, alerts_enabled, season_filter)
        VALUES (?, NULL, NULL, 10, 7, 1, 0)
    """, (message.from_user.id,))
    await message.answer(
        "🐦 <b>BAM – Birds Around Me</b>\n\n"
        "Чтобы начать, откройте <b>⚙️ Настройки</b> и укажите своё местоположение "
        "— через поиск по городу или GPS-геолокацию.\n\n"
        "Команды:\n/help — справка\n/cancel — отменить текущий ввод",
        reply_markup=await main_keyboard(message.from_user.id),
        parse_mode="HTML",
    )

@router.message(Command("cancel"))
async def cancel(message: Message, state: FSMContext):
    await state.clear()
    await message.answer("❌ Отменено.", reply_markup=await main_keyboard(message.from_user.id))

@router.message(Command("help"))
async def help_cmd(message: Message):
    ebird_text = "\n🗺 Хотспоты рядом — лучшие места для наблюдения птиц поблизости" if EBIRD_API_KEY else ""
    await message.answer(
        "🐦 <b>BAM – Birds Around Me</b>\n\n"
        "<b>Кнопки:</b>\n"
        "🐦 Сканировать — список птиц в радиусе\n"
        "📷 Определить птицу — пришлите фото, бот определит вид\n"
        "🚨 Редкие птицы — охраняемые и необычные виды рядом"
        + ebird_text + "\n"
        "⭐ Вишлист — уведомления об избранных птицах\n"
        "⚙️ Настройки — радиус, период, местоположение, фильтры\n\n"
        "<b>Inline-режим:</b>\n"
        "Введите <code>@birdsaroundmebot скворец</code> в любом чате.\n\n"
        "<b>Команды:</b>\n"
        "/cancel — выйти из режима ввода",
        parse_mode="HTML",
    )

# ================= ГЕОЛОКАЦИЯ =================
@router.message(F.location)
async def handle_location(message: Message, state: FSMContext):
    if not message.from_user:
        return
    await state.clear()
    lat = message.location.latitude
    lon = message.location.longitude
    await db_exec(
        "UPDATE users SET lat = ?, lon = ? WHERE telegram_id = ?",
        (lat, lon, message.from_user.id),
    )
    _invalidate_scan_cache(message.from_user.id)
    place = await reverse_geocode(lat, lon)
    await message.answer(
        f"✅ <b>Геолокация сохранена!</b>\n\n📍 {e(place)}\n\n"
        f"Теперь можно сканировать или вернуться в <b>⚙️ Настройки</b>.",
        reply_markup=await main_keyboard(message.from_user.id),
        parse_mode="HTML",
    )

# ================= УКАЗАТЬ ГОРОД (из настроек через callback) =================
@router.callback_query(F.data == "set_city")
async def settings_set_city(callback: CallbackQuery, state: FSMContext):
    await state.set_state(Form.waiting_city)
    await callback.message.answer(
        "🏠 Напишите название города или населённого пункта:\n\n"
        "Примеры: Москва 🔹 Ярославль 🔹 Helsinki\n\nЧтобы выйти, нажмите /cancel"
    )
    await callback.answer()

@router.callback_query(F.data == "set_location_request")
async def settings_set_location(callback: CallbackQuery):
    await callback.message.answer(
        "📍 Нажмите кнопку ниже, чтобы отправить геолокацию:",
        reply_markup=_location_request_keyboard(),
    )
    await callback.answer()

# Отмена из временной клавиатуры геолокации
@router.message(F.text == "❌ Отмена")
async def cancel_location_request(message: Message, state: FSMContext):
    await state.clear()
    await message.answer(
        "Отменено.",
        reply_markup=await main_keyboard(message.from_user.id),
    )

@router.message(Form.waiting_city)
async def handle_city_input(message: Message, state: FSMContext):
    if not message.from_user:
        return
    uid = message.from_user.id
    now = time()
    if now - _geocode_cooldown.get(uid, 0) < GEOCODE_COOLDOWN_SEC:
        await message.answer("⏳ Подождите секунду перед следующим поиском.")
        return
    _geocode_cooldown[uid] = now

    text = message.text.strip()
    if len(text) < 2:
        await message.answer("❌ Слишком короткое название. Введите хотя бы 2 символа.")
        return
    if len(text) > 100:
        await message.answer("❌ Слишком длинное название.")
        return
    lat, lon, display_name = await geocode_city(text)
    if lat is None:
        await message.answer(
            "❌ Не удалось найти город.\n"
            "Попробуйте точнее (например «Ярославль, Россия») или /cancel\n\n"
            "Также можно отправить геолокацию кнопкой 📍."
        )
        return
    await db_exec(
        "UPDATE users SET lat = ?, lon = ? WHERE telegram_id = ?",
        (lat, lon, uid),
    )
    _invalidate_scan_cache(uid)
    await state.clear()
    await message.answer(
        f"✅ <b>Местоположение сохранено!</b>\n\n📍 {e(display_name)}\nТеперь можно сканировать!",
        reply_markup=await main_keyboard(uid),
        parse_mode="HTML",
    )

# ================= 📷 ОПРЕДЕЛЕНИЕ ПТИЦЫ ПО ФОТО =================
@router.message(F.text == "📷 Определить птицу")
async def ask_for_photo(message: Message):
    await message.answer(
        "📷 <b>Определение птицы по фото</b>\n\n"
        "Просто пришлите фотографию птицы — я постараюсь определить вид!\n\n"
        "Советы для лучшего результата:\n"
        "• Птица должна быть чётко видна\n"
        "• Хорошее освещение\n"
        "• Фото птицы целиком лучше фрагмента",
        parse_mode="HTML",
    )

@router.message(F.photo)
async def handle_photo(message: Message):
    if not message.from_user:
        return
    uid     = message.from_user.id
    wait_ms = await message.answer("🔍 Анализирую фото...")

    # Получаем координаты пользователя для уточнения результата
    row = await db_fetch_one("SELECT lat, lon FROM users WHERE telegram_id = ?", (uid,))
    lat, lon = (row[0], row[1]) if row and row[0] else (None, None)

    # Скачиваем фото (берём наибольшее)
    photo   = message.photo[-1]
    file    = await bot.get_file(photo.file_id)
    file_url = f"https://api.telegram.org/file/bot{TOKEN}/{file.file_path}"
    try:
        async with http_session.get(file_url, timeout=aiohttp.ClientTimeout(total=15)) as r:
            r.raise_for_status()
            photo_bytes = await r.read()
    except Exception as ex:
        await wait_ms.delete()
        logger.error(f"Ошибка загрузки фото: {ex}")
        await message.answer("❌ Не удалось загрузить фото. Попробуйте ещё раз.")
        return

    results = await identify_bird_photo(photo_bytes, lat, lon)
    await wait_ms.delete()

    if not results:
        await message.answer(
            "😕 Не удалось определить вид птицы по этому фото.\n\n"
            "Попробуйте фото с лучшим освещением и более крупным планом птицы."
        )
        return

    text = "🐦 <b>Возможные виды:</b>\n\n"
    kb_rows = []
    for i, item in enumerate(results[:5], 1):
        t     = item.get("taxon", {})
        name  = t.get("preferred_common_name") or t.get("name", "Неизвестно")
        sci   = t.get("name", "")
        score = item.get("combined_score", 0)
        pct   = round(score * 100)
        # Полоска уверенности
        bar_len = round(pct / 10)
        bar = "█" * bar_len + "░" * (10 - bar_len)
        text += f"<b>{i}. {e(name)}</b> <i>{e(sci)}</i>\n{bar} {pct}%\n\n"
        tid = t.get("id")
        if tid:
            kb_rows.append([InlineKeyboardButton(
                text=f"{i}. {name}",
                callback_data=f"bird:{tid}:0",
            )])

    if lat is not None:
        text += "📍 <i>Результат уточнён по вашему местоположению</i>"
    else:
        text += "💡 <i>Укажите город или геолокацию для более точного определения</i>"

    kb_rows.append([InlineKeyboardButton(
        text="🐦 Открыть карточку первого вида",
        callback_data=f"bird:{results[0]['taxon']['id']}:0",
    )])

    await message.answer(
        text,
        parse_mode="HTML",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=kb_rows),
    )

# ================= СКАНИРОВАНИЕ =================
@router.message(F.text.startswith("🐦 Сканировать"))
async def scan(message: Message):
    if not message.from_user:
        return
    uid = message.from_user.id
    now = time()
    if now - _scan_cooldown.get(uid, 0) < SCAN_COOLDOWN_SEC:
        return await message.answer("⏳ Подождите немного перед следующим сканированием.")
    _scan_cooldown[uid] = now

    wait_msg = await message.answer("🔍 Ищу птиц рядом...")
    text, kb = await _build_scan_content(uid, page=1)
    await wait_msg.delete()

    if text is None:
        return await message.answer("❌ Сначала укажите город кнопкой «🏠 Город»!")
    await message.answer(text, parse_mode="HTML", reply_markup=kb)

@router.callback_query(F.data.startswith("scan_page:"))
async def scan_page_cb(callback: CallbackQuery):
    try:
        page = max(1, int(callback.data.split(":")[1]))
    except (ValueError, IndexError):
        await callback.answer("⚠️ Устаревшая кнопка.", show_alert=True)
        return
    text, kb = await _build_scan_content(callback.from_user.id, page=page)
    if text is None:
        await callback.answer("❌ Сначала укажите город!", show_alert=True)
        return
    if callback.message.photo or callback.message.document:
        await callback.message.answer(text, parse_mode="HTML", reply_markup=kb)
    else:
        try:
            await callback.message.edit_text(text, parse_mode="HTML", reply_markup=kb)
        except Exception:
            await callback.message.answer(text, parse_mode="HTML", reply_markup=kb)
    await callback.answer()

async def _build_scan_content(user_id: int, page: int):
    row = await db_fetch_one(
        "SELECT lat, lon, radius, period_days, season_filter FROM users WHERE telegram_id = ?",
        (user_id,)
    )
    if not row or not row[0]:
        return None, None

    lat, lon, radius, days, season_filter = row
    season_filter = bool(season_filter)

    cached_text, cached_species = _get_scan_cache(user_id, page)
    if cached_text is not None and cached_species is not None:
        total_pages = _get_total_pages_cached(user_id, page)
        return cached_text, _build_scan_keyboard(cached_species, page, total_pages)

    species, total = await get_species_counts(lat, lon, radius, days, page=page,
                                              season_filter=season_filter)
    if not species:
        if season_filter:
            return (f"😕 В этом радиусе пока нет наблюдений птиц "
                    f"за {current_season_name()}.\n"
                    f"Попробуйте отключить сезонный фильтр в ⚙️ Настройках."), None
        return "😕 В этом радиусе пока нет наблюдений птиц.", None

    total_pages  = max(1, (total + 9) // 10)
    season_note  = f"🌿 Сезонный фильтр: {current_season_name()}\n" if season_filter else ""
    text = (
        f"🐦 <b>Птицы рядом с вами</b>\n\n"
        f"Радиус: {radius} км · Период: {days} дн.\n"
        f"{season_note}"
        f"Страница {page} из {total_pages}\n\n"
    )
    for i, s in enumerate(species, start=(page - 1) * 10 + 1):
        name  = s["taxon"].get("preferred_common_name") or s["taxon"]["name"]
        count = s["count"]
        text += f"{i}. {e(name)} — {count} встреч\n"

    _set_scan_cache(user_id, page, text, species, total_pages)
    return text, _build_scan_keyboard(species, page, total_pages)

def _build_scan_keyboard(species: list, page: int, total_pages: int) -> InlineKeyboardMarkup:
    rows = []
    for s in species:
        name  = s["taxon"].get("preferred_common_name") or s["taxon"]["name"]
        count = s["count"]
        tid   = s["taxon"]["id"]
        rows.append([InlineKeyboardButton(
            text=f"{name} ({count})",
            callback_data=f"bird:{tid}:{page}",
        )])
    nav = []
    if page > 1:
        nav.append(InlineKeyboardButton(text="← Назад", callback_data=f"scan_page:{page - 1}"))
    if page < total_pages:
        nav.append(InlineKeyboardButton(text="Ещё →", callback_data=f"scan_page:{page + 1}"))
    if nav:
        rows.append(nav)
    return InlineKeyboardMarkup(inline_keyboard=rows)

# ================= КАРТОЧКА ПТИЦЫ =================
@router.callback_query(F.data.startswith("bird:"))
async def show_bird(callback: CallbackQuery):
    try:
        parts     = callback.data.split(":")
        taxon_id  = int(parts[1])
        back_page = int(parts[2]) if len(parts) > 2 else None
    except (ValueError, IndexError):
        await callback.answer("⚠️ Устаревшая кнопка.", show_alert=True)
        return

    row    = await db_fetch_one(
        "SELECT lat, lon, radius, period_days FROM users WHERE telegram_id = ?",
        (callback.from_user.id,),
    )
    in_fav = await db_fetch_one(
        "SELECT 1 FROM favorites WHERE telegram_id = ? AND taxon_id = ?",
        (callback.from_user.id, taxon_id),
    ) is not None

    if not row or not row[0]:
        await callback.answer("❌ Сначала укажите город!", show_alert=True)
        return

    lat, lon, radius, days = row

    obs, rare_result = await asyncio.gather(
        get_latest_observation_for_taxon(lat, lon, radius, days, taxon_id),
        get_rare_and_season(taxon_id, lat, lon, radius),
    )
    rare_emoji, rare_label, season_text, taxon_data = rare_result

    if not obs:
        await callback.message.answer("❌ Нет свежих наблюдений этого вида в радиусе.")
        await callback.answer()
        return

    name         = e(obs["taxon"].get("preferred_common_name") or obs["taxon"]["name"])
    sci          = e(obs["taxon"].get("name", ""))
    obs_lat, obs_lon = _parse_obs_coords(obs)
    ago          = time_ago(obs.get("time_observed_at") or obs.get("observed_on"))
    obs_url      = f"https://www.inaturalist.org/observations/{obs['id']}"
    dist_str     = (f"📍 {haversine(lat, lon, obs_lat, obs_lon)} км от вас\n"
                    if obs_lat is not None else "📍 Координаты скрыты автором\n")

    photo_medium   = get_photo_url(obs, "medium")
    photo_original = get_photo_url(obs, "original")

    family_name, order_name = _extract_taxonomy(taxon_data)
    taxonomy_str = ""
    if order_name or family_name:
        taxonomy_str = "🔬 " + " · ".join(filter(None, [e(order_name), e(family_name)])) + "\n"

    # Флаги инвазивности / эндемичности
    flags     = _extract_taxon_flags(taxon_data)
    flags_str = ("".join(f"{fl}\n" for fl in flags)) if flags else ""

    fav_text = "❌ Убрать из вишлиста" if in_fav else "⭐ В вишлист"
    fav_data = f"fav_remove:{taxon_id}" if in_fav else f"fav_add:{taxon_id}"

    text = f"🐦 <b>{name}</b>  <i>{sci}</i>\n"
    if taxonomy_str:
        text += taxonomy_str
    text += (
        f"\n{rare_emoji} {e(rare_label.capitalize())}\n"
        f"{dist_str}"
        f"🕒 {ago}\n"
    )
    if season_text:
        text += f"{season_text}\n"
    if flags_str:
        text += f"\n{flags_str}"
    text += "\nСамое свежее наблюдение в вашем радиусе."

    kb_rows = [[InlineKeyboardButton(text="Открыть на iNaturalist →", url=obs_url)]]
    if photo_original:
        kb_rows.append([InlineKeyboardButton(text="🔍 Фото в полном размере", url=photo_original)])
    kb_rows.append([InlineKeyboardButton(text=fav_text, callback_data=fav_data)])
    if back_page is not None and back_page > 0:
        kb_rows.append([InlineKeyboardButton(text="← К списку", callback_data=f"scan_page:{back_page}")])

    kb = InlineKeyboardMarkup(inline_keyboard=kb_rows)

    if photo_medium:
        await bot.send_photo(callback.from_user.id, photo_medium,
                             caption=text, reply_markup=kb, parse_mode="HTML")
    else:
        await callback.message.answer(text, reply_markup=kb, parse_mode="HTML")
    await callback.answer()

# ================= ВИШЛИСТ =================
@router.message(F.text.startswith("⭐ Вишлист"))
async def show_wishlist(message: Message):
    favs = await db_fetch_all(
        "SELECT taxon_id, taxon_name FROM favorites WHERE telegram_id = ?",
        (message.from_user.id,),
    )
    if not favs:
        await message.answer(
            "⭐ <b>Вишлист пуст</b>\n\n"
            "Здесь появятся птицы, за которыми вы следите. "
            "Бот уведомит вас, когда они окажутся рядом.\n\n"
            "Откройте карточку любой птицы через «🐦 Сканировать» и нажмите «⭐ В вишлист».",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[[
                InlineKeyboardButton(text="🐦 Перейти к сканированию", callback_data="goto_scan")
            ]])
        )
        return

    text    = "⭐ <b>Вишлист</b>\n\nНажмите на птицу, чтобы удалить её:\n\n"
    kb_rows = []
    for tid, name in favs:
        text += f"• {name}\n"
        kb_rows.append([InlineKeyboardButton(text=f"❌ {name}", callback_data=f"fav_remove:{tid}")])

    await message.answer(text, parse_mode="HTML",
                         reply_markup=InlineKeyboardMarkup(inline_keyboard=kb_rows))

@router.callback_query(F.data.startswith("fav_add:"))
async def fav_add(callback: CallbackQuery):
    uid      = callback.from_user.id
    taxon_id = int(callback.data.split(":")[1])

    ck  = (uid, taxon_id)
    now = time()
    if now - _fav_cooldown.get(ck, 0) < 3:
        await callback.answer("⏳ Подождите секунду...", show_alert=False)
        return
    _fav_cooldown[ck] = now

    name = await get_taxon_name(taxon_id)
    await db_exec(
        "INSERT OR IGNORE INTO favorites (telegram_id, taxon_id, taxon_name) VALUES (?, ?, ?)",
        (uid, taxon_id, name),
    )
    _invalidate_fav_count(uid)

    new_kb = _replace_fav_button(callback.message.reply_markup, taxon_id, added=True)
    try:
        if callback.message.photo:
            await callback.message.edit_caption(
                caption=callback.message.caption, reply_markup=new_kb, parse_mode="HTML"
            )
        else:
            await callback.message.edit_reply_markup(reply_markup=new_kb)
    except Exception:
        pass

    await bot.send_message(
        uid, f"⭐ <b>{e(name)}</b> добавлен(а) в вишлист.",
        reply_markup=await main_keyboard(uid),
        parse_mode="HTML",
    )
    await callback.answer("⭐ Добавлено!", show_alert=False)

@router.callback_query(F.data.startswith("fav_remove:"))
async def fav_remove(callback: CallbackQuery):
    uid      = callback.from_user.id
    taxon_id = int(callback.data.split(":")[1])
    await db_exec(
        "DELETE FROM favorites WHERE telegram_id = ? AND taxon_id = ?",
        (uid, taxon_id),
    )
    _invalidate_fav_count(uid)

    new_kb = _replace_fav_button(callback.message.reply_markup, taxon_id, added=False)
    try:
        if callback.message.photo:
            await callback.message.edit_caption(
                caption=callback.message.caption, reply_markup=new_kb, parse_mode="HTML"
            )
        else:
            await callback.message.edit_reply_markup(reply_markup=new_kb)
    except Exception:
        pass

    await callback.answer("❌ Удалено из вишлиста", show_alert=False)
    await bot.send_message(
        uid, "❌ Птица удалена из вишлиста.",
        reply_markup=await main_keyboard(uid),
    )

def _replace_fav_button(markup: InlineKeyboardMarkup | None,
                        taxon_id: int, added: bool) -> InlineKeyboardMarkup | None:
    if markup is None:
        return None
    new_text = "❌ Убрать из вишлиста" if added else "⭐ В вишлист"
    new_data = f"fav_remove:{taxon_id}" if added else f"fav_add:{taxon_id}"
    new_rows = []
    for row in markup.inline_keyboard:
        new_row = []
        for btn in row:
            if btn.callback_data in (f"fav_add:{taxon_id}", f"fav_remove:{taxon_id}"):
                new_row.append(InlineKeyboardButton(text=new_text, callback_data=new_data))
            else:
                new_row.append(btn)
        new_rows.append(new_row)
    return InlineKeyboardMarkup(inline_keyboard=new_rows)

# ================= 🗺 ХОТСПОТЫ =================
@router.message(F.text == "🗺 Хотспоты рядом")
async def show_hotspots(message: Message):
    if not message.from_user:
        return
    if not EBIRD_API_KEY:
        await message.answer("❌ Функция недоступна: не задан EBIRD_API_KEY.")
        return

    row = await db_fetch_one(
        "SELECT lat, lon, radius FROM users WHERE telegram_id = ?",
        (message.from_user.id,)
    )
    if not row or not row[0]:
        await message.answer("❌ Сначала укажите город кнопкой «🏠 Город»!")
        return

    lat, lon, radius = row
    wait_msg = await message.answer("🗺 Ищу лучшие места для наблюдений...")

    hotspots = await get_ebird_hotspots(lat, lon, dist=min(radius, 50))
    await wait_msg.delete()

    if not hotspots:
        await message.answer(
            "😕 Поблизости не найдено eBird-хотспотов.\n"
            "Попробуйте увеличить радиус в ⚙️ Настройках."
        )
        return

    text = "🗺 <b>Лучшие места для наблюдения птиц рядом</b>\n"
    text += f"<i>Данные eBird · Радиус ~{min(radius, 50)} км</i>\n\n"

    kb_rows = []
    for i, hs in enumerate(hotspots[:8], 1):
        name        = hs.get("locName", "Неизвестное место")
        species_all = hs.get("numSpeciesAllTime", 0)
        last_obs    = hs.get("latestObsDt", "")
        hs_lat      = hs.get("lat")
        hs_lon      = hs.get("lng")
        dist_str    = ""
        if hs_lat and hs_lon:
            dist = haversine(lat, lon, hs_lat, hs_lon)
            dist_str = f" · {dist} км"

        text += f"<b>{i}. {e(name)}</b>\n"
        text += f"🐦 {species_all} видов всего{dist_str}\n"
        if last_obs:
            text += f"🕒 Последнее наблюдение: {last_obs[:10]}\n"
        text += "\n"

        loc_id = hs.get("locId", "")
        if loc_id:
            kb_rows.append([InlineKeyboardButton(
                text=f"📍 {name[:40]}",
                url=f"https://ebird.org/hotspot/{loc_id}",
            )])

    await message.answer(text, parse_mode="HTML",
                         reply_markup=InlineKeyboardMarkup(inline_keyboard=kb_rows) if kb_rows else None)

# ================= НАСТРОЙКИ =================
def _build_settings_content(r: int, d: int, alerts: int, season: int,
                             location_name: str = "") -> tuple[str, InlineKeyboardMarkup]:
    alerts_label = "включены ✅" if alerts else "выключены ❌"
    season_label = f"включён ✅ ({current_season_name()})" if season else "выключен ❌"
    loc_str = f"\nМестоположение: <b>{e(location_name)}</b>" if location_name else ""
    text = (
        f"⚙️ <b>Настройки</b>\n"
        f"{loc_str}\n"
        f"Радиус: <b>{r} км</b>\n"
        f"Период: <b>{d} дней</b>\n"
        f"Уведомления: <b>{alerts_label}</b>\n"
        f"Сезонный фильтр: <b>{season_label}</b>"
    )

    def _r(val):
        return f"✅ {val} км" if val == r else f"{val} км"

    def _d(val, label):
        return f"✅ {label}" if val == d else label

    # Некликабельные заголовки визуально отличаются через «── ... ──»
    kb = InlineKeyboardMarkup(inline_keyboard=[
        # --- Местоположение ---
        [InlineKeyboardButton(text="── 🌍 Местоположение ──", callback_data="noop")],
        [InlineKeyboardButton(text="🏠 Ввести город",           callback_data="set_city"),
         InlineKeyboardButton(text="📍 Геолокация (GPS)",       callback_data="set_location_request")],
        # --- Радиус ---
        [InlineKeyboardButton(text="── 🌐 Радиус поиска ──",    callback_data="noop")],
        [InlineKeyboardButton(text=_r(5),  callback_data="set_r:5"),
         InlineKeyboardButton(text=_r(10), callback_data="set_r:10")],
        [InlineKeyboardButton(text=_r(25), callback_data="set_r:25"),
         InlineKeyboardButton(text=_r(50), callback_data="set_r:50")],
        [InlineKeyboardButton(text="✏️ Свой радиус",             callback_data="set_r:custom")],
        # --- Период ---
        [InlineKeyboardButton(text="── 🕗 Период наблюдений ──", callback_data="noop")],
        [InlineKeyboardButton(text=_d(1,  "24 ч"),    callback_data="set_d:1"),
         InlineKeyboardButton(text=_d(3,  "3 дня"),   callback_data="set_d:3")],
        [InlineKeyboardButton(text=_d(7,  "7 дней"),  callback_data="set_d:7"),
         InlineKeyboardButton(text=_d(30, "30 дней"), callback_data="set_d:30")],
        # --- Уведомления ---
        [InlineKeyboardButton(text="── 🗒 Уведомления и фильтры ──", callback_data="noop")],
        [InlineKeyboardButton(
            text="🔕 Выключить уведомления" if alerts else "🔔 Включить уведомления",
            callback_data="toggle_alerts",
        )],
        [InlineKeyboardButton(
            text=f"🌿 Сезонный фильтр: {'вкл ✅' if season else 'выкл ❌'}",
            callback_data="toggle_season",
        )],
    ])
    return text, kb

@router.message(F.text == "⚙️ Настройки")
async def settings(message: Message):
    row = await db_fetch_one(
        "SELECT radius, period_days, alerts_enabled, season_filter, lat, lon FROM users WHERE telegram_id = ?",
        (message.from_user.id,),
    ) or (10, 7, 1, 0, None, None)
    r, d, alerts, season, lat, lon = row
    location_name = ""
    if lat is not None and lon is not None:
        location_name = await reverse_geocode(lat, lon)
    text, kb = _build_settings_content(r, d, alerts, season, location_name)
    await message.answer(text, parse_mode="HTML", reply_markup=kb)

@router.callback_query(F.data == "noop")
async def noop(callback: CallbackQuery):
    await callback.answer()

@router.callback_query(F.data == "goto_scan")
async def goto_scan(callback: CallbackQuery):
    await callback.answer()
    uid = callback.from_user.id
    now = time()
    if now - _scan_cooldown.get(uid, 0) < SCAN_COOLDOWN_SEC:
        await callback.message.answer("⏳ Подождите немного перед следующим сканированием.")
        return
    _scan_cooldown[uid] = now
    wait_msg = await callback.message.answer("🔍 Ищу птиц рядом...")
    text, kb = await _build_scan_content(uid, page=1)
    await wait_msg.delete()
    if text is None:
        await callback.message.answer("❌ Сначала укажите город кнопкой «🏠 Город»!")
        return
    await callback.message.answer(text, parse_mode="HTML", reply_markup=kb)

@router.callback_query(F.data == "toggle_alerts")
async def toggle_alerts(callback: CallbackQuery):
    row     = await db_fetch_one(
        "SELECT radius, period_days, alerts_enabled, season_filter, lat, lon FROM users WHERE telegram_id = ?",
        (callback.from_user.id,),
    ) or (10, 7, 1, 0, None, None)
    r, d, current_alerts, season, lat, lon = row
    new_val = 0 if current_alerts else 1
    await db_exec(
        "UPDATE users SET alerts_enabled = ? WHERE telegram_id = ?",
        (new_val, callback.from_user.id),
    )
    location_name = await reverse_geocode(lat, lon) if lat else ""
    text, kb = _build_settings_content(r, d, new_val, season, location_name)
    try:
        await callback.message.edit_text(text, parse_mode="HTML", reply_markup=kb)
    except Exception:
        pass
    label = "включены ✅" if new_val else "выключены ❌"
    await callback.answer(f"🔔 Уведомления {label}", show_alert=False)

@router.callback_query(F.data == "toggle_season")
async def toggle_season(callback: CallbackQuery):
    row = await db_fetch_one(
        "SELECT radius, period_days, alerts_enabled, season_filter, lat, lon FROM users WHERE telegram_id = ?",
        (callback.from_user.id,),
    ) or (10, 7, 1, 0, None, None)
    r, d, alerts, current_season, lat, lon = row
    new_season = 0 if current_season else 1
    await db_exec(
        "UPDATE users SET season_filter = ? WHERE telegram_id = ?",
        (new_season, callback.from_user.id),
    )
    _invalidate_scan_cache(callback.from_user.id)
    location_name = await reverse_geocode(lat, lon) if lat else ""
    text, kb = _build_settings_content(r, d, alerts, new_season, location_name)
    try:
        await callback.message.edit_text(text, parse_mode="HTML", reply_markup=kb)
    except Exception:
        pass
    label = f"включён ({current_season_name()})" if new_season else "выключен"
    await callback.answer(f"🌿 Сезонный фильтр {label}", show_alert=False)

@router.callback_query(F.data.startswith("set_r:"))
async def set_radius(callback: CallbackQuery, state: FSMContext):
    value = callback.data.split(":")[1]
    if value == "custom":
        await state.set_state(Form.waiting_custom_radius)
        await callback.message.answer(
            "✏️ Введите радиус в километрах (1–200):\n\nНапример: <b>35</b>\n\nИли /cancel",
            parse_mode="HTML",
        )
        await callback.answer()
        return
    VALID_RADII = {5, 10, 25, 50}
    try:
        r = int(value)
    except ValueError:
        await callback.answer("⚠️ Недопустимое значение.", show_alert=True)
        return
    if r not in VALID_RADII:
        await callback.answer("⚠️ Недопустимое значение.", show_alert=True)
        return
    await db_exec("UPDATE users SET radius = ? WHERE telegram_id = ?", (r, callback.from_user.id))
    _invalidate_scan_cache(callback.from_user.id)
    row = await db_fetch_one(
        "SELECT radius, period_days, alerts_enabled, season_filter, lat, lon FROM users WHERE telegram_id = ?",
        (callback.from_user.id,),
    ) or (r, 7, 1, 0, None, None)
    _r, d, alerts, season, lat, lon = row
    location_name = await reverse_geocode(lat, lon) if lat else ""
    text, kb = _build_settings_content(_r, d, alerts, season, location_name)
    try:
        await callback.message.edit_text(text, parse_mode="HTML", reply_markup=kb)
    except Exception:
        pass
    await callback.answer(f"✅ Радиус: {r} км", show_alert=False)

@router.message(Form.waiting_custom_radius)
async def handle_custom_radius(message: Message, state: FSMContext):
    try:
        r = int(message.text.strip())
        if not 1 <= r <= 200:
            raise ValueError
    except ValueError:
        await message.answer("❌ Введите целое число от 1 до 200:")
        return
    await db_exec(
        "UPDATE users SET radius = ? WHERE telegram_id = ?", (r, message.from_user.id)
    )
    _invalidate_scan_cache(message.from_user.id)
    await state.clear()
    await message.answer(f"✅ Радиус установлен: {r} км",
                         reply_markup=await main_keyboard(message.from_user.id))

@router.callback_query(F.data.startswith("set_d:"))
async def set_days(callback: CallbackQuery):
    d = int(callback.data.split(":")[1])
    await db_exec("UPDATE users SET period_days = ? WHERE telegram_id = ?", (d, callback.from_user.id))
    _invalidate_scan_cache(callback.from_user.id)
    row = await db_fetch_one(
        "SELECT radius, period_days, alerts_enabled, season_filter, lat, lon FROM users WHERE telegram_id = ?",
        (callback.from_user.id,),
    ) or (10, d, 1, 0, None, None)
    r, _d, alerts, season, lat, lon = row
    location_name = await reverse_geocode(lat, lon) if lat else ""
    text, kb = _build_settings_content(r, _d, alerts, season, location_name)
    try:
        await callback.message.edit_text(text, parse_mode="HTML", reply_markup=kb)
    except Exception:
        pass
    await callback.answer(f"✅ Период: {d} дней", show_alert=False)

# ================= 🚨 РЕДКИЕ ПТИЦЫ =================
def _obs_within_hours(obs: dict, cutoff: datetime) -> bool:
    dt_str = obs.get("time_observed_at") or obs.get("observed_on") or ""
    if not dt_str:
        return False
    try:
        dt = datetime.fromisoformat(dt_str.replace("Z", "+00:00"))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt >= cutoff
    except Exception:
        return False

@router.message(F.text == "🚨 Редкие птицы")
async def manual_rare(message: Message):
    await check_rare_for_user(message.from_user.id, manual=True)

async def check_rare_for_user(telegram_id: int, manual: bool = False,
                               observations: list | None = None):
    row = await db_fetch_one(
        "SELECT lat, lon, radius, period_days FROM users WHERE telegram_id = ?", (telegram_id,)
    )
    if not row or not row[0]:
        if manual:
            await bot.send_message(telegram_id, "❌ Сначала укажи город!")
        return

    lat, lon, radius, days = row

    # iNaturalist наблюдения
    if manual:
        if observations is None:
            observations = await get_recent_observations(lat, lon, radius, days)
    else:
        if observations is None:
            d1_str = (datetime.now(timezone.utc) - timedelta(hours=AUTO_CHECK_WINDOW_HOURS)).date().isoformat()
            data   = await api_get(f"{API_BASE}/observations", {
                "lat": round(lat, 2), "lng": round(lon, 2), "radius": radius, "d1": d1_str,
                "iconic_taxa": "Aves", "locale": "ru",
                "per_page": 100, "order_by": "observed_on", "order": "desc",
            })
            observations = data.get("results", [])
        else:
            cutoff       = datetime.now(timezone.utc) - timedelta(hours=AUTO_CHECK_WINDOW_HOURS)
            observations = [obs for obs in observations if _obs_within_hours(obs, cutoff)]

    # eBird notable birds (только при ручном запросе или авто с ключом)
    ebird_notables = []
    if EBIRD_API_KEY:
        ebird_notables = await get_ebird_notable(lat, lon, dist=min(radius, 50))

    if not observations and not ebird_notables:
        if manual:
            await bot.send_message(telegram_id, "✅ Пока нет редких птиц в вашем радиусе.")
        return

    # Cooldown для авто-режима
    recent_notified: set[int] = set()
    if not manual:
        rows = await db_fetch_all(
            "SELECT taxon_id FROM rare_notifications "
            "WHERE telegram_id = ? AND notified_at > datetime('now', '-24 hours')",
            (telegram_id,),
        )
        recent_notified = {r[0] for r in rows}

    found_any  = False
    sent_count = 0
    now_str    = datetime.now(timezone.utc).isoformat()

    # --- iNaturalist: охраняемые/редкие виды ---
    taxon_count: dict[int, list] = defaultdict(list)
    for obs in observations:
        taxon_count[obs["taxon"]["id"]].append(obs)

    for tid, bird_obs in taxon_count.items():
        if not manual and sent_count >= 3:
            break
        obs = bird_obs[0]
        obs_lat, obs_lon = _parse_obs_coords(obs)
        if obs_lat is None:
            continue
        dist = haversine(lat, lon, obs_lat, obs_lon)
        if dist > radius:
            continue

        # --- Проверка редкости (одинакова для ручного и авто режимов) ---
        taxon_inline = obs.get("taxon", {})
        cs           = (taxon_inline.get("conservation_status") or {})
        status_code  = cs.get("status", "").lower()
        is_threatened = status_code in ("cr", "en", "vu") or bool(taxon_inline.get("threatened"))
        global_count  = taxon_inline.get("observations_count", 0)

        # Правило: не показываем глобально массовые виды (воробьи, голуби и т.п.),
        # если только они не охраняемые — тогда показываем всегда.
        if not is_threatened and global_count > RARITY_GLOBAL_COMMON_THRESHOLD:
            continue

        if not manual:
            # В авто-режиме — только строго охраняемые (CR/EN/VU), чтобы не спамить
            taxon_cached = _get_taxon_cached(tid)
            if taxon_cached and taxon_cached.get("results"):
                cs_cached = (taxon_cached["results"][0].get("conservation_status") or {})
                if cs_cached.get("status", "").lower() not in ("cr", "en", "vu"):
                    continue
            else:
                # Нет данных в кэше — используем inline-данные из наблюдения
                if not is_threatened:
                    continue
            if tid in recent_notified:
                continue

        # Определяем метку редкости для отображения
        if is_threatened:
            rarity_label = "охраняемый вид (CR/EN/VU)"
        elif global_count <= RARITY_LOCAL_RARE_THRESHOLD:
            rarity_label = "очень редко встречается"
        else:
            rarity_label = "редко встречается в этом районе"

        found_any = True
        name  = obs["taxon"].get("preferred_common_name") or obs["taxon"]["name"]
        ago   = time_ago(obs.get("time_observed_at") or obs.get("observed_on"))
        photo = get_photo_url(obs, "medium")
        url   = f"https://www.inaturalist.org/observations/{obs['id']}"
        text  = (
            f"🚨 <b>Редкое наблюдение рядом!</b>\n\n"
            f"<b>{e(name)}</b>\n📍 {dist} км от вас\n🕒 {ago}\n"
            f"<i>🔴 {e(rarity_label)} · iNaturalist</i>"
        )
        kb = InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(text="Открыть на iNaturalist →", url=url)
        ]])
        if photo:
            await bot.send_photo(telegram_id, photo, caption=text,
                                 reply_markup=kb, parse_mode="HTML")
        else:
            await bot.send_message(telegram_id, text, reply_markup=kb, parse_mode="HTML")

        if not manual:
            sent_count += 1
            try:
                await db_conn.execute(
                    "INSERT OR REPLACE INTO rare_notifications "
                    "(telegram_id, taxon_id, notified_at) VALUES (?, ?, ?)",
                    (telegram_id, tid, now_str),
                )
                await db_conn.commit()
            except Exception:
                logger.error(f"Ошибка rare_notifications для user {telegram_id}", exc_info=True)

    # --- eBird notable birds ---
    if ebird_notables and (manual or sent_count < 3):
        sent_ebird = 0
        # Дедупликация: не показывать виды, уже показанные из iNat
        shown_names: set[str] = set()

        for notable in ebird_notables:
            if not manual and (sent_count + sent_ebird) >= 3:
                break

            com_name = notable.get("comName", "")
            sci_name = notable.get("sciName", "")
            if not com_name:
                continue
            if com_name.lower() in shown_names:
                continue

            nb_lat = notable.get("lat")
            nb_lon = notable.get("lng")
            dist_str = ""
            if nb_lat and nb_lon:
                dist_nb = haversine(lat, lon, nb_lat, nb_lon)
                if dist_nb > radius * 1.5:
                    continue
                dist_str = f"📍 {dist_nb} км от вас\n"

            obs_dt  = notable.get("obsDt", "")[:10]
            how_many = notable.get("howMany")
            count_str = f" ({how_many} особ.)" if how_many else ""

            loc_name = notable.get("locName", "")
            text = (
                f"🚨 <b>Необычное наблюдение рядом!</b>\n\n"
                f"<b>{e(com_name)}</b> <i>{e(sci_name)}</i>{count_str}\n"
                f"{dist_str}"
                f"📅 {obs_dt}\n"
                f"📍 {e(loc_name)}\n"
                f"<i>Источник: eBird (необычный вид для этого района)</i>"
            )
            loc_id = notable.get("locId", "")
            url    = f"https://ebird.org/hotspot/{loc_id}" if loc_id else "https://ebird.org"
            kb = InlineKeyboardMarkup(inline_keyboard=[[
                InlineKeyboardButton(text="Открыть на eBird →", url=url)
            ]])
            await bot.send_message(telegram_id, text, reply_markup=kb, parse_mode="HTML")

            found_any = True
            shown_names.add(com_name.lower())
            sent_ebird += 1

    if manual and not found_any:
        await bot.send_message(telegram_id, "✅ Пока нет редких птиц в вашем радиусе.")

# ================= ВИШЛИСТ ПРОВЕРКА =================
async def check_watchlist_for_user(telegram_id: int, observations: list | None = None):
    row  = await db_fetch_one(
        "SELECT lat, lon, radius, period_days FROM users WHERE telegram_id = ?", (telegram_id,)
    )
    favs = await db_fetch_all(
        "SELECT taxon_id, taxon_name, last_notified_at FROM favorites WHERE telegram_id = ?",
        (telegram_id,),
    )
    if not row or not row[0] or not favs:
        return

    lat, lon, radius, days = row
    taxon_ids = [f[0] for f in favs]

    if observations:
        latest_map: dict = {}
        watched_set = set(taxon_ids)
        for obs in observations:
            tid = obs["taxon"]["id"]
            if tid in watched_set and tid not in latest_map:
                latest_map[tid] = obs
        missing = [tid for tid in taxon_ids if tid not in latest_map]
        if missing:
            extra = await get_batch_watchlist_observations(lat, lon, radius, days, missing)
            latest_map.update(extra)
    else:
        latest_map = await get_batch_watchlist_observations(lat, lon, radius, days, taxon_ids)

    now_str = datetime.now(timezone.utc).isoformat()

    for taxon_id, taxon_name, last_notified_at in favs:
        obs = latest_map.get(taxon_id)
        if not obs:
            continue
        age = days_since(last_notified_at)
        if age is not None and age < 1:
            continue
        obs_lat, obs_lon = _parse_obs_coords(obs)
        if obs_lat is None:
            continue

        dist  = haversine(lat, lon, obs_lat, obs_lon)
        ago   = time_ago(obs.get("time_observed_at") or obs.get("observed_on"))
        photo = get_photo_url(obs, "medium")
        url   = f"https://www.inaturalist.org/observations/{obs['id']}"
        text  = (
            f"⭐ <b>Птица из вишлиста замечена рядом!</b>\n\n"
            f"<b>{e(taxon_name)}</b>\n📍 {dist} км от вас\n🕒 {ago}"
        )
        kb = InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(text="Открыть на iNaturalist →", url=url)
        ]])
        if photo:
            await bot.send_photo(telegram_id, photo, caption=text,
                                 reply_markup=kb, parse_mode="HTML")
        else:
            await bot.send_message(telegram_id, text, reply_markup=kb, parse_mode="HTML")

        await db_exec(
            "UPDATE favorites SET last_notified_at = ? WHERE telegram_id = ? AND taxon_id = ?",
            (now_str, telegram_id, taxon_id),
        )

# ================= 🔥 BIRD ALERT =================
async def check_bird_alert_for_user(telegram_id: int, lat: float, lon: float,
                                     radius: int, days: int,
                                     observations: list | None = None):
    if observations is None:
        observations = await get_recent_observations(lat, lon, radius, days)
    if not observations:
        return

    now_str = datetime.now(timezone.utc).isoformat()
    history = {r[0]: r[1] for r in await db_fetch_all(
        "SELECT taxon_id, last_seen_at FROM species_history WHERE telegram_id = ?", (telegram_id,)
    )}

    seen: dict[int, dict] = {}
    for obs in observations:
        tid = obs["taxon"]["id"]
        if tid not in seen:
            obs_lat, obs_lon = _parse_obs_coords(obs)
            if obs_lat is not None:
                seen[tid] = obs

    notified_tids: set[int] = set()
    alerts_sent = 0

    for tid, obs in seen.items():
        absent_days = days_since(history.get(tid))
        if absent_days is None or absent_days >= BIRD_ALERT_DAYS:
            if alerts_sent < 3:
                months_absent = (absent_days // 30) if absent_days else None
                name  = obs["taxon"].get("preferred_common_name") or obs["taxon"]["name"]
                ago   = time_ago(obs.get("time_observed_at") or obs.get("observed_on"))
                photo = get_photo_url(obs, "medium")
                url   = f"https://www.inaturalist.org/observations/{obs['id']}"
                header = (f"🔥 <b>впервые за {months_absent} мес. в вашем районе замечен:</b>"
                          if months_absent else "🔥 <b>впервые замечен в вашем районе:</b>")
                text  = f"{header}\n\n<b>{e(name)}</b>\n📍 Радиус: {radius} км\n🕒 {ago}"
                kb    = InlineKeyboardMarkup(inline_keyboard=[[
                    InlineKeyboardButton(text="Открыть наблюдение →", url=url)
                ]])
                if photo:
                    await bot.send_photo(telegram_id, photo, caption=text,
                                         reply_markup=kb, parse_mode="HTML")
                else:
                    await bot.send_message(telegram_id, text, reply_markup=kb, parse_mode="HTML")

                notified_tids.add(tid)
                alerts_sent += 1

    try:
        for tid in notified_tids:
            await db_conn.execute(
                """INSERT INTO species_history (telegram_id, taxon_id, last_seen_at)
                   VALUES (?, ?, ?)
                   ON CONFLICT(telegram_id, taxon_id)
                   DO UPDATE SET last_seen_at = excluded.last_seen_at""",
                (telegram_id, tid, now_str),
            )
        for tid in seen:
            if tid not in notified_tids:
                await db_conn.execute(
                    "INSERT OR IGNORE INTO species_history (telegram_id, taxon_id, last_seen_at) "
                    "VALUES (?, ?, ?)",
                    (telegram_id, tid, now_str),
                )
        await db_conn.commit()
    except Exception:
        await db_conn.rollback()
        logger.error(f"Ошибка species_history для user {telegram_id}", exc_info=True)

# ================= ПЛАНИРОВЩИК =================
async def _run_checks_for_user(uid: int, lat: float, lon: float, radius: int, days: int):
    try:
        observations = await get_recent_observations(lat, lon, radius, days)
        await asyncio.gather(
            check_rare_for_user(uid, manual=False, observations=observations),
            check_bird_alert_for_user(uid, lat, lon, radius, days, observations=observations),
            check_watchlist_for_user(uid, observations=observations),
            return_exceptions=True,
        )
    except Exception:
        logger.error(f"Ошибка при проверке пользователя {uid}", exc_info=True)

async def scheduled_checks():
    users = await db_fetch_all(
        "SELECT telegram_id, lat, lon, radius, period_days "
        "FROM users WHERE alerts_enabled = 1 AND lat IS NOT NULL"
    )
    logger.info(f"scheduled_checks: запуск для {len(users)} пользователей")

    for i in range(0, len(users), SCHEDULER_BATCH_SIZE):
        batch = users[i:i + SCHEDULER_BATCH_SIZE]
        tasks = [_run_checks_for_user(*u) for u in batch]
        try:
            await asyncio.wait_for(
                asyncio.gather(*tasks, return_exceptions=True),
                timeout=90,
            )
        except asyncio.TimeoutError:
            logger.warning(f"scheduled_checks: таймаут для пачки {i // SCHEDULER_BATCH_SIZE + 1}")
        if i + SCHEDULER_BATCH_SIZE < len(users):
            await asyncio.sleep(SCHEDULER_BATCH_DELAY)

# ================= INLINE-РЕЖИМ =================
@router.inline_query()
async def inline_search(inline_query: InlineQuery):
    query = inline_query.query.strip()
    if len(query) < 2:
        await inline_query.answer(
            [], cache_time=5,
            switch_pm_text="Введите название птицы...",
            switch_pm_parameter="start",
        )
        return

    uid  = inline_query.from_user.id

    # Получаем координаты пользователя для показа ближайшего наблюдения
    user_row = await db_fetch_one(
        "SELECT lat, lon, radius, period_days FROM users WHERE telegram_id = ?", (uid,)
    )

    taxa    = await search_taxa_by_name(query)
    results = []

    # Если есть координаты, параллельно запрашиваем ближайшие наблюдения
    nearest_obs: dict[int, dict] = {}
    if user_row and user_row[0] and taxa:
        lat, lon, radius, days = user_row
        taxon_ids = [t["id"] for t in taxa[:5]]
        batch_obs = await get_batch_watchlist_observations(lat, lon, radius, days, taxon_ids)
        nearest_obs = batch_obs

    for t in taxa[:8]:
        name     = t.get("preferred_common_name") or t.get("name", "")
        sci_name = t.get("name", "")
        tid      = t["id"]
        thumb    = None
        if t.get("default_photo"):
            thumb = t["default_photo"].get("square_url") or t["default_photo"].get("medium_url")

        inat_url = f"https://www.inaturalist.org/taxa/{tid}"

        # Описание: добавляем ближайшее наблюдение если есть
        description = sci_name
        nearest_text = ""
        if tid in nearest_obs and user_row:
            obs  = nearest_obs[tid]
            ago  = time_ago(obs.get("time_observed_at") or obs.get("observed_on"))
            obs_lat, obs_lon = _parse_obs_coords(obs)
            if obs_lat is not None:
                dist = haversine(user_row[0], user_row[1], obs_lat, obs_lon)
                nearest_text = f"\n\n📍 Замечена {dist} км от вас · {ago}"
                description  = f"{sci_name} · {dist} км от вас, {ago}"

        obs_link = ""
        if tid in nearest_obs:
            obs_id   = nearest_obs[tid].get("id")
            obs_link = f"\n🔗 <a href='https://www.inaturalist.org/observations/{obs_id}'>Последнее наблюдение</a>"

        msg_text = (
            f"🐦 <b>{e(name)}</b>  <i>{e(sci_name)}</i>"
            f"{nearest_text}\n\n"
            f"🔗 <a href='{inat_url}'>Открыть на iNaturalist</a>"
            f"{obs_link}\n\n"
            f"Слежу за птицами → @{BOT_USERNAME}"
        )
        results.append(InlineQueryResultArticle(
            id=str(uuid.uuid4()),
            title=name,
            description=description,
            thumbnail_url=thumb,
            input_message_content=InputTextMessageContent(
                message_text=msg_text, parse_mode="HTML",
            ),
        ))

    await inline_query.answer(results, cache_time=60)

# ================= ЗАПУСК =================
async def main():
    global http_session, db_conn, BOT_USERNAME, _api_semaphore

    try:
        await init_db()
    except Exception:
        logger.critical("Не удалось инициализировать БД", exc_info=True)
        raise

    db_conn = await aiosqlite.connect(DB_NAME, check_same_thread=False)
    await db_conn.execute("PRAGMA journal_mode=WAL")
    await db_conn.execute("PRAGMA synchronous=NORMAL")
    db_conn.row_factory = aiosqlite.Row

    http_session   = aiohttp.ClientSession(
        connector=aiohttp.TCPConnector(limit=API_SEMAPHORE_LIMIT)
    )
    _api_semaphore = asyncio.Semaphore(API_SEMAPHORE_LIMIT)

    bot_info     = await bot.get_me()
    BOT_USERNAME = bot_info.username
    logger.info(f"Бот запущен как @{BOT_USERNAME}")

    if EBIRD_API_KEY:
        logger.info("eBird API ключ найден — хотспоты и notable birds активны")
    else:
        logger.info("EBIRD_API_KEY не задан — eBird-функции отключены")

    scheduler = AsyncIOScheduler()
    scheduler.add_job(scheduled_checks,        "interval", hours=1,
                      max_instances=1, misfire_grace_time=300)
    scheduler.add_job(_cleanup_scan_cache,      "interval", minutes=10)
    scheduler.add_job(_cleanup_cooldowns,        "interval", minutes=5)
    scheduler.add_job(_cleanup_rare_notifications, "interval", hours=6)
    scheduler.start()

    logger.info("🚀 BAM бот запущен!")
    try:
        await dp.start_polling(bot)
    finally:
        scheduler.shutdown(wait=False)
        await http_session.close()
        await db_conn.close()
        logger.info("✅ Бот остановлен, ресурсы освобождены.")

if __name__ == "__main__":
    asyncio.run(main())
