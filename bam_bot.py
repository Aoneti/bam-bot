import asyncio
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
from tenacity import retry, stop_after_attempt, wait_exponential, retry_if_exception_type

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

API_BASE = "https://api.inaturalist.org/v1"
DB_NAME  = "bam_users.db"

BIRD_ALERT_DAYS     = 90    # дней без наблюдений → «давно не появлялась»
SCAN_CACHE_TTL      = 240   # секунд — кэш страниц сканирования
OBS_CACHE_TTL       = 900   # секунд (15 мин) — общий кэш наблюдений по координатам
TAXON_CACHE_TTL     = 6 * 3600   # 6 часов — данные таксона
HIST_CACHE_TTL      = 24 * 3600  # 24 часа — гистограмма сезонности
SCHEDULER_BATCH_SIZE  = 5
SCHEDULER_BATCH_DELAY = 2.0   # секунды между пачками в планировщике
SCAN_COOLDOWN_SEC     = 30    # кулдаун кнопки «Сканировать»
API_SEMAPHORE_LIMIT   = 5     # макс. одновременных запросов к iNaturalist

bot     = Bot(token=TOKEN)
storage = MemoryStorage()
dp      = Dispatcher(storage=storage)
router  = Router()
dp.include_router(router)

BOT_USERNAME: str          = ""
_api_semaphore: asyncio.Semaphore = None  # инициализируется в main()

# ================= FSM СОСТОЯНИЯ =================
class Form(StatesGroup):
    waiting_city          = State()
    waiting_custom_radius = State()

# ================= RATE LIMIT =================
_scan_cooldown: dict[int, float]   = {}
_fav_cooldown:  dict[tuple, float] = {}  # (uid, taxon_id) → timestamp

# ================= ГЛОБАЛЬНЫЕ ОБЪЕКТЫ =================
http_session: aiohttp.ClientSession = None
db_conn:      aiosqlite.Connection  = None

# ================= LRU-КЭШ =================
class LRUCache:
    """Простой LRU-кэш с максимальным числом записей."""
    def __init__(self, max_size: int = 200):
        self._cache: OrderedDict = OrderedDict()
        self._max   = max_size

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
# Кэши таксонов и гистограмм — LRU с ограничением размера (нет утечки памяти)
_taxon_cache_lru = LRUCache(max_size=500)
_hist_cache_lru  = LRUCache(max_size=500)

# ================= КЭШ СТРАНИЦ СКАНИРОВАНИЯ (по user_id) =================
_scan_cache:       dict[tuple, tuple]       = {}
_scan_total_pages: dict[int, dict[int, int]] = {}

def _get_scan_cache(user_id: int, page: int):
    key   = (user_id, page)
    entry = _scan_cache.get(key)
    if entry and (time() - entry[0]) < SCAN_CACHE_TTL:
        return entry[1], entry[2]
    return None, None

def _set_scan_cache(user_id: int, page: int, text: str, species: list, total_pages: int):
    _scan_cache[(user_id, page)] = (time(), text, species)
    _scan_total_pages.setdefault(user_id, {})[page] = total_pages

def _get_total_pages_cached(user_id: int, page: int) -> int:
    return (_scan_total_pages.get(user_id) or {}).get(page, 1)

def _invalidate_scan_cache(user_id: int):
    for k in [k for k in _scan_cache if k[0] == user_id]:
        del _scan_cache[k]
    _scan_total_pages.pop(user_id, None)

# ================= ОБЩИЙ КЭШ НАБЛЮДЕНИЙ ПО КООРДИНАТАМ =================
# Ключ: (lat_rounded, lon_rounded, radius, days) — round(,2) даёт точность ~1 км.
# Все пользователи из одного района получают один ответ из кэша.
_obs_cache: dict[tuple, tuple] = {}

def _coord_key(lat: float, lon: float, radius: int, days: int) -> tuple:
    return (round(lat, 2), round(lon, 2), radius, days)

def _get_obs_cache(lat: float, lon: float, radius: int, days: int):
    entry = _obs_cache.get(_coord_key(lat, lon, radius, days))
    if entry and (time() - entry[0]) < OBS_CACHE_TTL:
        return entry[1]
    return None

def _set_obs_cache(lat: float, lon: float, radius: int, days: int, results: list):
    _obs_cache[_coord_key(lat, lon, radius, days)] = (time(), results)

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

# ================= ОЧИСТКА ПАМЯТИ =================
def _cleanup_scan_cache():
    now   = time()
    stale = [k for k, v in _scan_cache.items()
             if isinstance(k[1], int) and (now - v[0]) > SCAN_CACHE_TTL]
    for k in stale:
        del _scan_cache[k]
    stale_obs = [k for k, v in _obs_cache.items() if (now - v[0]) > OBS_CACHE_TTL]
    for k in stale_obs:
        del _obs_cache[k]
    logger.debug(f"cache cleanup: scan={len(stale)}, obs={len(stale_obs)}")

def _cleanup_cooldowns():
    threshold = time() - 120
    for k in [k for k, v in _scan_cooldown.items() if v < threshold]:
        del _scan_cooldown[k]
    for k in [k for k, v in _fav_cooldown.items() if v < threshold]:
        del _fav_cooldown[k]

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
                notify_hours   TEXT    DEFAULT 'all',
                last_check     TEXT
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
        # Cooldown-таблица для уведомлений о редких птицах.
        # Не даёт слать одно и то же чаще раза в 24 часа.
        await db.execute("""
            CREATE TABLE IF NOT EXISTS rare_notifications (
                telegram_id  INTEGER,
                taxon_id     INTEGER,
                notified_at  TEXT,
                PRIMARY KEY (telegram_id, taxon_id)
            )
        """)
        for migration in [
            "ALTER TABLE users     ADD COLUMN notify_hours TEXT DEFAULT 'all'",
            "ALTER TABLE favorites ADD COLUMN last_notified_at TEXT",
        ]:
            try:
                await db.execute(migration)
            except Exception:
                pass
        await db.execute("CREATE INDEX IF NOT EXISTS idx_fav_user     ON favorites(telegram_id)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_users_alerts ON users(alerts_enabled, lat)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_history      ON species_history(telegram_id)")
        await db.commit()

# ================= HELPERS ДЛЯ БД =================
async def db_fetch_one(sql: str, params: tuple = ()):
    async with db_conn.execute(sql, params) as cur:
        return await cur.fetchone()

async def db_fetch_all(sql: str, params: tuple = ()):
    async with db_conn.execute(sql, params) as cur:
        return await cur.fetchall()

async def db_exec(sql: str, params: tuple = ()):
    await db_conn.execute(sql, params)
    await db_conn.commit()

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
    except Exception as e:
        logger.error(f"Geocoding error: {e}")
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
        delta = datetime.now(timezone.utc) - dt
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

# ================= БАЗОВЫЙ API-ЗАПРОС С RETRY И СЕМАФОРОМ =================
@retry(
    stop=stop_after_attempt(3),
    wait=wait_exponential(multiplier=1, min=1, max=8),
    retry=retry_if_exception_type((aiohttp.ClientError, asyncio.TimeoutError)),
    reraise=True,
)
async def _raw_api_get(url: str, params: dict) -> dict:
    # Семафор ограничивает одновременные запросы к iNaturalist (не более API_SEMAPHORE_LIMIT)
    async with _api_semaphore:
        async with http_session.get(url, params=params,
                                    timeout=aiohttp.ClientTimeout(total=10)) as r:
            r.raise_for_status()
            return await r.json()

async def api_get(url: str, params: dict) -> dict:
    try:
        return await _raw_api_get(url, params)
    except Exception as e:
        logger.error(f"API request failed [{url}]: {e}")
        return {}

# ================= API iNATURALIST =================
async def get_species_counts(lat, lon, radius, days, page=1):
    d1   = (datetime.now().date() - timedelta(days=days)).isoformat()
    data = await api_get(f"{API_BASE}/observations/species_counts", {
        "lat": round(lat, 2), "lng": round(lon, 2), "radius": radius, "d1": d1,
        "iconic_taxa": "Aves", "locale": "ru",
        "per_page": 10, "page": page, "order_by": "observations_count",
    })
    return data.get("results", []), data.get("total_results", 0)

async def get_recent_observations(lat, lon, radius, days) -> list:
    """Наблюдения с общим кэшем по координатам.
    10 пользователей из одного района → 1 запрос к API вместо 10.
    """
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
    """Данные таксона с кэшем — используется во всех местах вместо прямого запроса."""
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

# ================= ИЗВЛЕЧЕНИЕ СЕМЕЙСТВА И ОТРЯДА =================
def _extract_taxonomy(taxon_data: dict) -> tuple[str, str]:
    """Возвращает (семейство, отряд) из данных таксона без доп. запросов.
    iNaturalist включает список ancestors прямо в ответ /taxa/{id}.
    """
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

# ================= РЕДКОСТЬ И СЕЗОННОСТЬ (КОМБИНИРОВАННАЯ ЛОГИКА) =================
async def get_rare_and_season(taxon_id: int, lat: float, lon: float, radius: int):
    d1_year = (datetime.now().date() - timedelta(days=365)).isoformat()

    taxon_cached = _get_taxon_cached(taxon_id)
    hist_cached  = _get_hist_cached(taxon_id, lat, lon, radius)

    # Собираем только недостающие запросы
    tasks = [
        api_get(f"{API_BASE}/observations/species_counts", {
            "lat": round(lat, 2), "lng": round(lon, 2), "radius": radius, "d1": d1_year,
            "taxon_id": taxon_id, "iconic_taxa": "Aves", "per_page": 1,
        }),
    ]
    if taxon_cached is None:
        tasks.append(api_get(f"{API_BASE}/taxa/{taxon_id}", {"locale": "ru"}))
    if hist_cached is None:
        tasks.append(api_get(f"{API_BASE}/observations/histogram", {
            "taxon_id": taxon_id,
            "lat": round(lat, 2), "lng": round(lon, 2), "radius": radius,
            "date_field": "observed_on", "interval": "month_of_year",
        }))

    api_results = await asyncio.gather(*tasks)
    idx = 0
    yearly_data = api_results[idx]; idx += 1

    if taxon_cached is None:
        taxon_data = api_results[idx]; idx += 1
        _set_taxon_cache(taxon_id, taxon_data)
    else:
        taxon_data = taxon_cached

    if hist_cached is None:
        season_data = api_results[idx]
        _set_hist_cache(taxon_id, lat, lon, radius, season_data)
    else:
        season_data = hist_cached

    # --- КОМБИНИРОВАННАЯ ЛОГИКА РЕДКОСТИ ---
    # Локальные наблюдения за год
    local_count = 0
    if yearly_data.get("results"):
        local_count = yearly_data["results"][0].get("count", 0)

    # Статус охраны и глобальное число наблюдений — из данных таксона, без доп. запросов
    is_threatened = False
    global_count  = 0
    if taxon_data.get("results"):
        t             = taxon_data["results"][0]
        cs            = (t.get("conservation_status") or {})
        is_threatened = cs.get("status", "").lower() in ("cr", "en", "vu")
        global_count  = t.get("observations_count", 0)

    # Правила (в порядке приоритета):
    # 1. Охраняемый (CR/EN/VU) → всегда 🔴
    # 2. Глобально > 10 000 набл. → 🟢 (зеленушка, синица — никогда не будут красными)
    # 3. Глобально ≤ 10 000 и локально ≤ 5 → 🔴 редкая в этом районе
    # 4. Глобально ≤ 10 000 и локально 6–20 → 🟡 нечасто встречается
    # 5. Иначе → 🟢 обычная редкость
    if is_threatened:
        rare_emoji, rare_label = "🔴", "охраняемый вид"
    elif global_count > 10_000:
        rare_emoji, rare_label = "🟢", "обычная редкость"
    elif local_count <= 5:
        rare_emoji, rare_label = "🔴", "редкая в этом районе"
    elif local_count <= 20:
        rare_emoji, rare_label = "🟡", "нечасто встречается"
    else:
        rare_emoji, rare_label = "🟢", "обычная редкость"

    # --- СЕЗОННОСТЬ ---
    MONTHS      = ["янв","фев","мар","апр","май","июн","июл","авг","сен","окт","ноя","дек"]
    season_text = ""
    raw_hist    = season_data.get("results") or {}
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

# ================= ГЛАВНАЯ КЛАВИАТУРА =================
async def main_keyboard(user_id: int) -> ReplyKeyboardMarkup:
    """Динамическая клавиатура — счётчик вишлиста обновляется при каждом вызове."""
    rows      = await db_fetch_all(
        "SELECT COUNT(*) FROM favorites WHERE telegram_id = ?", (user_id,)
    )
    fav_count = rows[0][0] if rows else 0
    fav_label = f"⭐ Вишлист ({fav_count})" if fav_count else "⭐ Вишлист"
    return ReplyKeyboardMarkup(
        keyboard=[
	    [KeyboardButton(text="🐦 Сканировать")],
            [KeyboardButton(text="🚨 Проверить редких птиц"), KeyboardButton(text=fav_label)],
            [KeyboardButton(text="📍 Отправить геолокацию", request_location=True), KeyboardButton(text="🏠 Указать город")],
            [KeyboardButton(text="⚙️ Настройки")],
        ],
        resize_keyboard=True,
    )

def _static_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [KeyboardButton(text="🐦 Сканировать")],
	    [KeyboardButton(text="🚨 Проверить редких птиц"), KeyboardButton(text="⭐ Вишлист")],
	    [KeyboardButton(text="📍 Отправить геолокацию", request_location=True), KeyboardButton(text="🏠 Указать город")],
	    [KeyboardButton(text="⚙️ Настройки")],
        ],
        resize_keyboard=True,
    )

# ================= ГЛОБАЛЬНЫЙ ОБРАБОТЧИК ОШИБОК =================
@router.errors()
async def global_error_handler(event: ErrorEvent):
    logger.error(f"Необработанное исключение: {event.exception}", exc_info=True)
    try:
        update = event.update
        if update.message:
            await update.message.answer("⚠️ Что-то пошло не так. Попробуй ещё раз.")
        elif update.callback_query:
            await update.callback_query.answer("⚠️ Ошибка. Попробуй позже.", show_alert=True)
    except Exception:
        pass

# ================= СТАРТ / ОТМЕНА =================
@router.message(Command("start"))
async def start(message: Message, state: FSMContext):
    await state.clear()
    await db_exec("""
        INSERT OR IGNORE INTO users
        (telegram_id, lat, lon, radius, period_days, alerts_enabled, notify_hours, last_check)
        VALUES (?, NULL, NULL, 10, 7, 1, 'all', NULL)
    """, (message.from_user.id,))
    await message.answer(
        "🐦 <b>BAM – Birds Around Me</b>\n\n"
        "Нажмите «🏠 Указать город» или «📍 Отправить геолокацию» для начала!\n\n"
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
    await message.answer(
        "🐦 <b>BAM – Birds Around Me</b>\n\n"
        "<b>Кнопки:</b>\n"
        "🐦 Сканировать — список птиц в радиусе\n"
        "🚨 Проверить редких птиц — показывает редкие в выбранном радиусе виды\n"
        "⭐ Вишлист — каждую птицу можно добавить в избранное. Вам будут приходить уведомления об их появлении поблизости\n"
        "🏠 Город — задать населённый пункт\n"
        "📍 Геолокация — передать координаты\n"
        "⚙️ Настройки — радиус, период, уведомления\n\n"
        "<b>Использовать бота в чатах:</b>\n"
        "Введите <code>@birdsaroundmebot скворец</code> (или другой вид) в любом чате.\n\n"
        "<b>Команды:</b>\n"
        "/cancel — выйти из режима ввода",
        parse_mode="HTML",
    )

# ================= ГЕОЛОКАЦИЯ =================
@router.message(F.location)
async def handle_location(message: Message, state: FSMContext):
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
        f"✅ <b>Геолокация сохранена!</b>\n\n📍 {place}\nТеперь можно сканировать!",
        reply_markup=await main_keyboard(message.from_user.id),
        parse_mode="HTML",
    )

# ================= УКАЗАТЬ ГОРОД (FSM) =================
@router.message(F.text == "🏠 Указать город")
async def request_city(message: Message, state: FSMContext):
    await state.set_state(Form.waiting_city)
    await message.answer(
        "🏠 Напишите название города или населённого пункта:\n\n"
        "Примеры: Москва 🔹 Ярославль 🔹 Helsinki\n\nЧтобы выйти, нажмите /cancel или /help для вызова меню справки."
    )

@router.message(Form.waiting_city)
async def handle_city_input(message: Message, state: FSMContext):
    text = message.text.strip()
    if len(text) > 100:
        await message.answer("❌ Слишком длинное название. Попробуй короче.")
        return
    lat, lon, display_name = await geocode_city(text)
    if lat is None:
        await message.answer(
            "❌ Не удалось найти город.\n"
            "Попробуй точнее (например «Ярославль, Россия») или /cancel"
        )
        return
    await db_exec(
        "UPDATE users SET lat = ?, lon = ? WHERE telegram_id = ?",
        (lat, lon, message.from_user.id),
    )
    _invalidate_scan_cache(message.from_user.id)
    await state.clear()
    await message.answer(
        f"✅ <b>Местоположение сохранено!</b>\n\n📍 {display_name}\nТеперь можно сканировать!",
        reply_markup=await main_keyboard(message.from_user.id),
        parse_mode="HTML",
    )

# ================= СКАНИРОВАНИЕ С ПАГИНАЦИЕЙ И КЭШЕМ =================
@router.message(F.text.startswith("🐦 Сканировать"))
async def scan(message: Message):
    uid = message.from_user.id
    now = time()
    if now - _scan_cooldown.get(uid, 0) < SCAN_COOLDOWN_SEC:
        return await message.answer("⏳ Подождите немного перед следующим сканированием.")
    _scan_cooldown[uid] = now

    wait_msg = await message.answer("🔍 Ищу птиц рядом...")
    text, kb = await _build_scan_content(uid, page=1)
    await wait_msg.delete()

    if text is None:
        return await message.answer("❌ Сначала укажи город кнопкой «🏠 Указать город»!")
    await message.answer(text, parse_mode="HTML", reply_markup=kb)

@router.callback_query(F.data.startswith("scan_page:"))
async def scan_page_cb(callback: CallbackQuery):
    page     = int(callback.data.split(":")[1])
    text, kb = await _build_scan_content(callback.from_user.id, page=page)
    if text is None:
        await callback.answer("❌ Сначала укажи город!", show_alert=True)
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
        "SELECT lat, lon, radius, period_days FROM users WHERE telegram_id = ?", (user_id,)
    )
    if not row or not row[0]:
        return None, None

    lat, lon, radius, days = row

    cached_text, cached_species = _get_scan_cache(user_id, page)
    if cached_text is not None and cached_species is not None:
        total_pages = _get_total_pages_cached(user_id, page)
        return cached_text, _build_scan_keyboard(cached_species, page, total_pages)

    species, total = await get_species_counts(lat, lon, radius, days, page=page)
    if not species:
        return "😕 В этом радиусе пока нет наблюдений птиц.", None

    total_pages = max(1, (total + 9) // 10)
    text = (
        f"🐦 <b>Птицы рядом с вами</b>\n\n"
        f"Радиус: {radius} км · Период: {days} дн.\n"
        f"Страница {page} из {total_pages}\n\n"
    )
    for i, s in enumerate(species, start=(page - 1) * 10 + 1):
        name  = s["taxon"].get("preferred_common_name") or s["taxon"]["name"]
        count = s["count"]
        text += f"{i}. {name} — {count} набл.\n"

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
        nav.append(InlineKeyboardButton(text="Ещё →",   callback_data=f"scan_page:{page + 1}"))
    if nav:
        rows.append(nav)
    return InlineKeyboardMarkup(inline_keyboard=rows)

# ================= КАРТОЧКА ПТИЦЫ =================
@router.callback_query(F.data.startswith("bird:"))
async def show_bird(callback: CallbackQuery):
    parts     = callback.data.split(":")
    taxon_id  = int(parts[1])
    back_page = int(parts[2]) if len(parts) > 2 else None

    row    = await db_fetch_one(
        "SELECT lat, lon, radius, period_days FROM users WHERE telegram_id = ?",
        (callback.from_user.id,),
    )
    in_fav = await db_fetch_one(
        "SELECT 1 FROM favorites WHERE telegram_id = ? AND taxon_id = ?",
        (callback.from_user.id, taxon_id),
    ) is not None

    if not row or not row[0]:
        await callback.answer("❌ Сначала укажи город!", show_alert=True)
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

    name         = obs["taxon"].get("preferred_common_name") or obs["taxon"]["name"]
    sci          = obs["taxon"].get("name", "")
    obs_lat, obs_lon = _parse_obs_coords(obs)
    ago          = time_ago(obs.get("time_observed_at") or obs.get("observed_on"))
    obs_url      = f"https://www.inaturalist.org/observations/{obs['id']}"
    dist_str     = (f"📍 {haversine(lat, lon, obs_lat, obs_lon)} км от вас\n"
                    if obs_lat is not None else "📍 Координаты скрыты автором\n")

    photo_medium = photo_original = None
    if obs.get("photos"):
        base           = obs["photos"][0]["url"]
        photo_medium   = base.replace("square", "medium")
        photo_original = base.replace("square", "original")

    # Семейство и отряд — из кэшированных данных таксона, без доп. запросов
    family_name, order_name = _extract_taxonomy(taxon_data)
    taxonomy_str = ""
    if order_name or family_name:
        taxonomy_str = "🔬 " + " · ".join(filter(None, [order_name, family_name])) + "\n"

    fav_text = "❌ Убрать из вишлиста" if in_fav else "⭐ В вишлист"
    fav_data = f"fav_remove:{taxon_id}" if in_fav else f"fav_add:{taxon_id}"

    text = (
        f"🐦 <b>{name}</b>  <i>{sci}</i>\n\n"
        f"{rare_emoji} {rare_label.capitalize()}\n"
        f"{dist_str}"
        f"🕒 {ago}\n"
    )
    if taxonomy_str:
        text += taxonomy_str
    if season_text:
        text += f"{season_text}\n"
    text += "\nСамое свежее наблюдение в вашем радиусе."

    kb_rows = [[InlineKeyboardButton(text="Открыть на iNaturalist →", url=obs_url)]]
    if photo_original:
        kb_rows.append([InlineKeyboardButton(text="🔍 Фото в полном размере", url=photo_original)])
    kb_rows.append([InlineKeyboardButton(text=fav_text, callback_data=fav_data)])
    if back_page is not None:
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
            "⭐ Вишлист пуст.\n\n"
            "Откройте карточку птицы и нажмите «⭐ В вишлист» — "
            "бот будет уведомлять вас, когда она появится рядом!"
        )
        return

    text    = "⭐ <b>Ваш вишлист</b>\n\nНажмите на птицу, чтобы удалить её:\n\n"
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
        await callback.answer("⏳ Подожди секунду...", show_alert=False)
        return
    _fav_cooldown[ck] = now

    name = await get_taxon_name(taxon_id)
    await db_exec(
        "INSERT OR IGNORE INTO favorites (telegram_id, taxon_id, taxon_name) VALUES (?, ?, ?)",
        (uid, taxon_id, name),
    )

    # Обновляем кнопку в карточке
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

    await callback.answer(f"⭐ {name} добавлен(а) в вишлист!", show_alert=False)

    # Обновляем счётчик в главной клавиатуре — пользователь сразу видит изменение
    await bot.send_message(
        uid, f"⭐ <b>{name}</b> добавлен(а) в вишлист.",
        reply_markup=await main_keyboard(uid),
        parse_mode="HTML",
    )

@router.callback_query(F.data.startswith("fav_remove:"))
async def fav_remove(callback: CallbackQuery):
    uid      = callback.from_user.id
    taxon_id = int(callback.data.split(":")[1])
    await db_exec(
        "DELETE FROM favorites WHERE telegram_id = ? AND taxon_id = ?",
        (uid, taxon_id),
    )

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

    # Обновляем счётчик в главной клавиатуре
    await bot.send_message(
        uid, "❌ Птица удалена из вишлиста.",
        reply_markup=await main_keyboard(uid),
    )

def _replace_fav_button(markup: InlineKeyboardMarkup | None,
                        taxon_id: int, added: bool) -> InlineKeyboardMarkup | None:
    if markup is None:
        return None
    new_text = "❌ Убрать из вишлиста" if added else "⭐ В вишлист"
    new_data = f"fav_remove:{taxon_id}"   if added else f"fav_add:{taxon_id}"
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

# ================= НАСТРОЙКИ =================
def _build_settings_content(r: int, d: int, alerts: int) -> tuple[str, InlineKeyboardMarkup]:
    """Возвращает (текст, клавиатура) для меню настроек.
    Вынесено в отдельную функцию, чтобы и при открытии, и при toggle_alerts
    меню строилось по одному и тому же коду с актуальными данными.
    """
    alerts_label = "включены ✅" if alerts else "выключены ❌"
    text = (
        f"⚙️ <b>Настройки</b>\n\n"
        f"Радиус: <b>{r} км</b>\n"
        f"Период: <b>{d} дней</b>\n"
        f"Уведомления: <b>{alerts_label}</b>"
    )

    def _r(val):
        return f"✅ {val} км" if val == r else f"{val} км"

    def _d(val, label):
        return f"✅ {label}" if val == d else label

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🌐 Радиус",    callback_data="noop")],
        [InlineKeyboardButton(text=_r(5),  callback_data="set_r:5"),
         InlineKeyboardButton(text=_r(10), callback_data="set_r:10")],
        [InlineKeyboardButton(text=_r(25), callback_data="set_r:25"),
         InlineKeyboardButton(text=_r(50), callback_data="set_r:50")],
        [InlineKeyboardButton(text="✏️ Свой радиус", callback_data="set_r:custom")],
        [InlineKeyboardButton(text="🕒 Период",    callback_data="noop")],
        [InlineKeyboardButton(text=_d(1,  "24 ч"),    callback_data="set_d:1"),
         InlineKeyboardButton(text=_d(3,  "3 дня"),   callback_data="set_d:3")],
        [InlineKeyboardButton(text=_d(7,  "7 дней"),  callback_data="set_d:7"),
         InlineKeyboardButton(text=_d(30, "30 дней"), callback_data="set_d:30")],
        [InlineKeyboardButton(text="🔔 Уведомления", callback_data="noop")],
        [InlineKeyboardButton(
            text="🔕 Выключить уведомления" if alerts else "🔔 Включить уведомления",
            callback_data="toggle_alerts",
        )],
    ])
    return text, kb

@router.message(F.text == "⚙️ Настройки")
async def settings(message: Message):
    row = await db_fetch_one(
        "SELECT radius, period_days, alerts_enabled FROM users WHERE telegram_id = ?",
        (message.from_user.id,),
    ) or (10, 7, 1)
    text, kb = _build_settings_content(*row)
    await message.answer(text, parse_mode="HTML", reply_markup=kb)

@router.callback_query(F.data == "noop")
async def noop(callback: CallbackQuery):
    await callback.answer()

@router.callback_query(F.data == "toggle_alerts")
async def toggle_alerts(callback: CallbackQuery):
    row     = await db_fetch_one(
        "SELECT radius, period_days, alerts_enabled FROM users WHERE telegram_id = ?",
        (callback.from_user.id,),
    ) or (10, 7, 1)
    r, d, current = row
    new_val = 0 if current else 1
    await db_exec(
        "UPDATE users SET alerts_enabled = ? WHERE telegram_id = ?",
        (new_val, callback.from_user.id),
    )
    # Перестраиваем меню с новым состоянием и обновляем сообщение прямо в чате
    text, kb = _build_settings_content(r, d, new_val)
    try:
        await callback.message.edit_text(text, parse_mode="HTML", reply_markup=kb)
    except Exception:
        pass
    label = "включены ✅" if new_val else "выключены ❌"
    await callback.answer(f"🔔 Уведомления {label}", show_alert=False)

@router.callback_query(F.data.startswith("set_r:"))
async def set_radius(callback: CallbackQuery, state: FSMContext):
    value = callback.data.split(":")[1]
    if value == "custom":
        await state.set_state(Form.waiting_custom_radius)
        await callback.message.answer(
            "✏️ Введи радиус в километрах (1–200):\n\nНапример: <b>35</b>\n\nИли /cancel",
            parse_mode="HTML",
        )
        await callback.answer()
        return
    r = int(value)
    await db_exec("UPDATE users SET radius = ? WHERE telegram_id = ?", (r, callback.from_user.id))
    _invalidate_scan_cache(callback.from_user.id)
    await callback.message.edit_text(f"✅ Радиус обновлён: {r} км")
    await bot.send_message(
        callback.from_user.id, "⚙️ Настройки сохранены.",
        reply_markup=await main_keyboard(callback.from_user.id),
    )
    await callback.answer()

@router.message(Form.waiting_custom_radius)
async def handle_custom_radius(message: Message, state: FSMContext):
    try:
        r = int(message.text.strip())
        if not 1 <= r <= 200:
            raise ValueError
    except ValueError:
        await message.answer("❌ Введи целое число от 1 до 200:")
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
    await callback.message.edit_text(f"✅ Период обновлён: {d} дней")
    await bot.send_message(
        callback.from_user.id, "⚙️ Настройки сохранены.",
        reply_markup=await main_keyboard(callback.from_user.id),
    )
    await callback.answer()

# ================= ПРОВЕРКА РЕДКИХ ПТИЦ =================
@router.message(F.text == "🚨 Проверить редких птиц")
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

    # При ручном запросе — полный период пользователя (из общего кэша).
    # При авто-уведомлении — только последние 3 часа, чтобы не повторять одно и то же каждый час.
    if manual:
        if observations is None:
            observations = await get_recent_observations(lat, lon, radius, days)
    else:
        d1_str = (datetime.now(timezone.utc) - timedelta(hours=3)).date().isoformat()
        data   = await api_get(f"{API_BASE}/observations", {
            "lat": round(lat, 2), "lng": round(lon, 2), "radius": radius, "d1": d1_str,
            "iconic_taxa": "Aves", "locale": "ru",
            "per_page": 100, "order_by": "observed_on", "order": "desc",
        })
        observations = data.get("results", [])

    if not observations:
        if manual:
            await bot.send_message(telegram_id, "✅ Пока нет редких птиц в твоём радиусе.")
        return

    # Cooldown: какие виды уже получали уведомление за последние 24 часа
    recent_notified: set[int] = set()
    if not manual:
        rows = await db_fetch_all(
            "SELECT taxon_id FROM rare_notifications "
            "WHERE telegram_id = ? AND notified_at > datetime('now', '-24 hours')",
            (telegram_id,),
        )
        recent_notified = {r[0] for r in rows}

    taxon_count: dict[int, list] = defaultdict(list)
    for obs in observations:
        taxon_count[obs["taxon"]["id"]].append(obs)

    found_any  = False
    sent_count = 0
    now_str    = datetime.now(timezone.utc).isoformat()

    for tid, bird_obs in taxon_count.items():
        # Лимит 3 авто-уведомления за один запуск планировщика
        if not manual and sent_count >= 3:
            break

        if len(bird_obs) != 1:
            continue

        obs = bird_obs[0]
        obs_lat, obs_lon = _parse_obs_coords(obs)
        if obs_lat is None:
            continue
        dist = haversine(lat, lon, obs_lat, obs_lon)
        if dist > radius:
            continue

        # Фильтр редкости: только охраняемые виды CR/EN/VU.
        # Исключает зеленушек и других обычных птиц с единственным локальным наблюдением.
        if not manual:
            taxon_data = _get_taxon_cached(tid)
            if taxon_data and taxon_data.get("results"):
                cs     = (taxon_data["results"][0].get("conservation_status") or {})
                status = cs.get("status", "").lower()
                if status not in ("cr", "en", "vu"):
                    continue
            else:
                # Нет данных в кэше — пропускаем, не делаем лишний API-запрос
                continue

            # Cooldown: не слать повторно раньше 24 часов
            if tid in recent_notified:
                continue

        found_any = True
        name  = obs["taxon"].get("preferred_common_name") or obs["taxon"]["name"]
        ago   = time_ago(obs.get("time_observed_at") or obs.get("observed_on"))
        photo = obs["photos"][0]["url"].replace("square", "medium") if obs.get("photos") else None
        url   = f"https://www.inaturalist.org/observations/{obs['id']}"
        text  = (
            f"🚨 <b>Редкое наблюдение рядом!</b>\n\n"
            f"<b>{name}</b>\n📍 {dist} км от вас\n🕒 {ago}"
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
                logger.error(f"Ошибка записи rare_notifications для user {telegram_id}", exc_info=True)

    if manual and not found_any:
        await bot.send_message(telegram_id, "✅ Пока нет редких птиц в твоём радиусе.")

# ================= ПРОВЕРКА ВИШЛИСТА =================
async def check_watchlist_for_user(telegram_id: int):
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
    taxon_ids  = [f[0] for f in favs]
    latest_map = await get_batch_watchlist_observations(lat, lon, radius, days, taxon_ids)
    now_str    = datetime.now(timezone.utc).isoformat()

    for taxon_id, taxon_name, last_notified_at in favs:
        obs = latest_map.get(taxon_id)
        if not obs:
            continue
        if days_since(last_notified_at) is not None and days_since(last_notified_at) < 1:
            continue
        obs_lat, obs_lon = _parse_obs_coords(obs)
        if obs_lat is None:
            continue

        dist  = haversine(lat, lon, obs_lat, obs_lon)
        ago   = time_ago(obs.get("time_observed_at") or obs.get("observed_on"))
        photo = obs["photos"][0]["url"].replace("square", "medium") if obs.get("photos") else None
        url   = f"https://www.inaturalist.org/observations/{obs['id']}"
        text  = (
            f"⭐ <b>Птица из вишлиста замечена рядом!</b>\n\n"
            f"<b>{taxon_name}</b>\n📍 {dist} км от вас\n🕒 {ago}"
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

    # notified_tids — птицы, которым отправили уведомление.
    # last_seen_at обновляем ТОЛЬКО для них.
    # Остальные (лимит 3) сохранят старую дату и попадут в очередь на следующий час.
    notified_tids: set[int] = set()
    alerts_sent = 0

    for tid, obs in seen.items():
        absent_days = days_since(history.get(tid))
        if absent_days is None or absent_days >= BIRD_ALERT_DAYS:
            if alerts_sent < 3:
                months_absent = (absent_days // 30) if absent_days else None
                name  = obs["taxon"].get("preferred_common_name") or obs["taxon"]["name"]
                ago   = time_ago(obs.get("time_observed_at") or obs.get("observed_on"))
                photo = obs["photos"][0]["url"].replace("square", "medium") if obs.get("photos") else None
                url   = f"https://www.inaturalist.org/observations/{obs['id']}"
                header = (f"🔥 <b>впервые за {months_absent} мес. в вашем районе замечен:</b>"
                          if months_absent else "🔥 <b>впервые замечен в вашем районе:</b>")
                text  = f"{header}\n\n<b>{name}</b>\n📍 Радиус: {radius} км\n🕒 {ago}"
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
            # Обновляем дату только тем, кто получил уведомление
            await db_conn.execute(
                """INSERT INTO species_history (telegram_id, taxon_id, last_seen_at)
                   VALUES (?, ?, ?)
                   ON CONFLICT(telegram_id, taxon_id)
                   DO UPDATE SET last_seen_at = excluded.last_seen_at""",
                (telegram_id, tid, now_str),
            )
        for tid in seen:
            if tid not in notified_tids:
                # Новые виды добавляем в историю только если записи ещё нет,
                # чтобы они появились в системе, но не потеряли «долг» по уведомлению
                await db_conn.execute(
                    "INSERT OR IGNORE INTO species_history (telegram_id, taxon_id, last_seen_at) "
                    "VALUES (?, ?, ?)",
                    (telegram_id, tid, now_str),
                )
        await db_conn.commit()
    except Exception:
        await db_conn.rollback()
        logger.error(f"Ошибка при обновлении species_history для user {telegram_id}", exc_info=True)

# ================= ПЛАНИРОВЩИК =================
async def _run_checks_for_user(uid: int, lat: float, lon: float, radius: int, days: int):
    """Загружаем наблюдения один раз — общий кэш по координатам делает это бесплатным
    для пользователей из одного района."""
    try:
        observations = await get_recent_observations(lat, lon, radius, days)
        await asyncio.gather(
            check_rare_for_user(uid, manual=False, observations=observations),
            check_bird_alert_for_user(uid, lat, lon, radius, days, observations=observations),
            check_watchlist_for_user(uid),
            return_exceptions=True,
        )
    except Exception:
        logger.error(f"Ошибка при проверке пользователя {uid}", exc_info=True)

async def scheduled_checks():
    """Каждый час проверяет всех пользователей с включёнными уведомлениями."""
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
            switch_pm_text="Введи название птицы...",
            switch_pm_parameter="start",
        )
        return

    taxa    = await search_taxa_by_name(query)
    results = []
    for t in taxa[:8]:
        name     = t.get("preferred_common_name") or t.get("name", "")
        sci_name = t.get("name", "")
        tid      = t["id"]
        thumb    = None
        if t.get("default_photo"):
            thumb = t["default_photo"].get("square_url") or t["default_photo"].get("medium_url")

        inat_url = f"https://www.inaturalist.org/taxa/{tid}"
        msg_text = (
            f"🐦 <b>{name}</b>  <i>{sci_name}</i>\n\n"
            f"🔗 <a href='{inat_url}'>Открыть на iNaturalist</a>\n\n"
            f"Проверь, есть ли эта птица рядом → @{BOT_USERNAME}"
        )
        results.append(InlineQueryResultArticle(
            id=str(uuid.uuid4()),
            title=name,
            description=sci_name,
            thumbnail_url=thumb,
            input_message_content=InputTextMessageContent(
                message_text=msg_text, parse_mode="HTML",
            ),
        ))

    await inline_query.answer(results, cache_time=60)

# ================= ЗАПУСК =================
async def main():
    global http_session, db_conn, BOT_USERNAME, _api_semaphore

    await init_db()

    db_conn = await aiosqlite.connect(DB_NAME, check_same_thread=False)
    await db_conn.execute("PRAGMA journal_mode=WAL")
    await db_conn.execute("PRAGMA synchronous=NORMAL")
    db_conn.row_factory = aiosqlite.Row

    http_session   = aiohttp.ClientSession()
    _api_semaphore = asyncio.Semaphore(API_SEMAPHORE_LIMIT)

    bot_info     = await bot.get_me()
    BOT_USERNAME = bot_info.username
    logger.info(f"Бот запущен как @{BOT_USERNAME}")

    scheduler = AsyncIOScheduler()
    scheduler.add_job(scheduled_checks,    "interval", hours=1)
    scheduler.add_job(_cleanup_scan_cache, "interval", minutes=10)
    scheduler.add_job(_cleanup_cooldowns,  "interval", minutes=5)
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
