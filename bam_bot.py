import asyncio
from contextlib import asynccontextmanager
import hashlib
import html as html_module
import io
import json
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
from aiogram.exceptions import (
    TelegramAPIError,
    TelegramBadRequest,
    TelegramForbiddenError,
    TelegramNetworkError,
    TelegramRetryAfter,
    TelegramServerError,
)
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

# ================= НАСТРОЙКИ =================
TOKEN = os.environ.get("BOT_TOKEN", "")
if not TOKEN:
    raise RuntimeError("Переменная окружения BOT_TOKEN не задана!")

EBIRD_API_KEY = os.environ.get("EBIRD_API_KEY", "")  # необязательный

# ================= ЛОГИРОВАНИЕ И ЗАЩИТА СЕКРЕТОВ =================
def _redact_secrets_in_text(text: str) -> str:
    if not isinstance(text, str) or not text:
        return text
    for secret in (TOKEN, EBIRD_API_KEY):
        if secret and secret in text:
            text = text.replace(secret, "***REDACTED***")
    return text

class _SecretRedactingFilter(logging.Filter):
    """Очищает record.msg, record.args и record.exc_text от BOT_TOKEN и EBIRD_API_KEY."""
    def filter(self, record: logging.LogRecord) -> bool:
        if isinstance(record.msg, str):
            record.msg = _redact_secrets_in_text(record.msg)
        if record.args:
            if isinstance(record.args, dict):
                record.args = {
                    k: (_redact_secrets_in_text(v) if isinstance(v, str) else v)
                    for k, v in record.args.items()
                }
            elif isinstance(record.args, tuple):
                sanitized_args = []
                for arg in record.args:
                    val = str(arg) if not isinstance(arg, (int, float)) else arg
                    if isinstance(val, str):
                        val = _redact_secrets_in_text(val)
                    sanitized_args.append(val)
                record.args = tuple(sanitized_args)
        if isinstance(record.exc_text, str):
            record.exc_text = _redact_secrets_in_text(record.exc_text)
        return True

class _SecretRedactingFormatter(logging.Formatter):
    """Гарантирует удаление секретов из отформатированного текста и любого traceback (exc_info)."""
    def formatException(self, ei) -> str:
        formatted = super().formatException(ei)
        return _redact_secrets_in_text(formatted)

    def format(self, record: logging.LogRecord) -> str:
        formatted = super().format(record)
        return _redact_secrets_in_text(formatted)

_log_formatter = _SecretRedactingFormatter("%(asctime)s %(levelname)s %(message)s")
_secret_filter = _SecretRedactingFilter()

_stream_handler = logging.StreamHandler()
_stream_handler.setFormatter(_log_formatter)
_stream_handler.addFilter(_secret_filter)

_file_handler = logging.FileHandler("bam_bot.log", encoding="utf-8")
_file_handler.setFormatter(_log_formatter)
_file_handler.addFilter(_secret_filter)

logging.basicConfig(
    level=logging.INFO,
    handlers=[_stream_handler, _file_handler],
)
logger = logging.getLogger(__name__)
logger.addFilter(_secret_filter)

API_BASE    = "https://api.inaturalist.org/v1"
EBIRD_BASE  = "https://api.ebird.org/v2"
DB_NAME     = "bam_users.db"

BIRD_ALERT_DAYS         = 90
SCAN_CACHE_TTL          = 240
OBS_CACHE_TTL           = 900
TAXON_CACHE_TTL         = 6 * 3600
HIST_CACHE_TTL          = 24 * 3600
EBIRD_NOTABLE_TTL       = 1800        # 30 минут
GEOCODE_CACHE_TTL       = 7 * 24 * 3600
SCHEDULER_BATCH_SIZE    = 20
SCHEDULER_BATCH_DELAY   = 0.5
SCAN_COOLDOWN_SEC       = 30
GEOCODE_COOLDOWN_SEC    = 5
API_SEMAPHORE_LIMIT     = 5
EBIRD_SEMAPHORE_LIMIT   = 3
TG_SEND_SEMAPHORE_LIMIT = 15
NOMINATIM_MIN_INTERVAL  = 1.1
AUTO_CHECK_WINDOW_HOURS = 3
LOCATION_RESET_DIST_KM  = 5.0

RARITY_GLOBAL_COMMON_THRESHOLD  = 10_000
RARITY_LOCAL_RARE_THRESHOLD     = 5
RARITY_LOCAL_UNCOMMON_THRESHOLD = 20

CURRENT_MONTH = datetime.now(timezone.utc).month

bot     = Bot(token=TOKEN)
storage = MemoryStorage()
dp      = Dispatcher(storage=storage)
router  = Router()
dp.include_router(router)

BOT_USERNAME: str                       = ""
_api_semaphore: asyncio.Semaphore       = None
_ebird_semaphore: asyncio.Semaphore     = None
_tg_send_semaphore: asyncio.Semaphore   = None
_nominatim_lock: asyncio.Lock           = asyncio.Lock()
_nominatim_last_req_ts: float           = 0.0
_db_lock: asyncio.Lock                  = asyncio.Lock()

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

_geocode_cache         = LRUCache(max_size=200)
_reverse_geocode_cache = LRUCache(max_size=500)
_taxa_search_cache     = LRUCache(max_size=100)
_taxon_cache_lru       = LRUCache(max_size=500)
_hist_cache_lru        = LRUCache(max_size=500)
_ebird_notable_cache   = LRUCache(max_size=200)

# ================= КЭШ СКАНИРОВАНИЯ =================
_scan_cache:       LRUCache                  = LRUCache(max_size=1000)
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
    if isinstance(data, dict) and "results" in data:
        _taxon_cache_lru.set(taxon_id, (time(), data))

# ================= КЭШ ГИСТОГРАММ =================
def _get_hist_cached(taxon_id: int, lat: float, lon: float, radius: int):
    key   = (taxon_id, round(lat, 2), round(lon, 2), radius)
    entry = _hist_cache_lru.get(key)
    if entry and (time() - entry[0]) < HIST_CACHE_TTL:
        return entry[1]
    return None

def _set_hist_cache(taxon_id: int, lat: float, lon: float, radius: int, data: dict):
    if isinstance(data, dict) and "results" in data:
        _hist_cache_lru.set((taxon_id, round(lat, 2), round(lon, 2), radius), (time(), data))

# ================= ОЧИСТКА =================
def _cleanup_scan_cache():
    now   = time()
    stale = [k for k, v in _scan_cache._cache.items()
             if isinstance(k[1], int) and (now - v[0]) > SCAN_CACHE_TTL]
    for k in stale:
        del _scan_cache._cache[k]
    active_users = {k[0] for k in _scan_cache._cache}
    for uid in [u for u in _scan_total_pages if u not in active_users]:
        _scan_total_pages.pop(uid, None)
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
    for k in [k for k, v in _geocode_cooldown.items() if v < threshold]:
        del _geocode_cooldown[k]

async def _cleanup_rare_notifications():
    try:
        async with db_transaction() as tx:
            await tx.execute(
                "DELETE FROM rare_notifications WHERE notified_at < datetime('now', '-48 hours')"
            )
            await tx.execute(
                "DELETE FROM seen_rare_observations WHERE notified_at < datetime('now', '-35 days')"
            )
            await tx.execute(
                "DELETE FROM notification_queue WHERE status IN ('sent', 'failed', 'cancelled') "
                "AND updated_at < datetime('now', '-35 days')"
            )
    except Exception:
        logger.error("Ошибка при очистке rare_notifications", exc_info=True)

# ================= БАЗА ДАННЫХ И ТРАНЗАКЦИИ =================
async def _apply_schema(db: aiosqlite.Connection):
    await db.execute("PRAGMA journal_mode=WAL")
    await db.execute("PRAGMA synchronous=NORMAL")
    await db.execute("PRAGMA busy_timeout=5000")
    await db.execute("""
        CREATE TABLE IF NOT EXISTS users (
            telegram_id         INTEGER PRIMARY KEY,
            lat                 REAL,
            lon                 REAL,
            radius              INTEGER DEFAULT 10,
            period_days         INTEGER DEFAULT 7,
            alerts_enabled      INTEGER DEFAULT 1,
            season_filter       INTEGER DEFAULT 0,
            history_initialized INTEGER DEFAULT 0
        )
    """)
    await db.execute("""
        CREATE TABLE IF NOT EXISTS favorites (
            telegram_id      INTEGER,
            taxon_id         INTEGER,
            taxon_name       TEXT,
            last_notified_at TEXT,
            last_obs_id      INTEGER,
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
            obs_key      TEXT,
            PRIMARY KEY (telegram_id, taxon_id)
        )
    """)
    await db.execute("""
        CREATE TABLE IF NOT EXISTS seen_rare_observations (
            telegram_id  INTEGER,
            obs_key      TEXT,
            taxon_key    TEXT,
            sci_name     TEXT,
            notified_at  TEXT,
            PRIMARY KEY (telegram_id, obs_key)
        )
    """)
    await db.execute("""
        CREATE TABLE IF NOT EXISTS notification_queue (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            telegram_id  INTEGER NOT NULL,
            notif_type   TEXT NOT NULL,
            dedup_key    TEXT NOT NULL,
            taxon_id     INTEGER,
            obs_id       TEXT,
            sci_name     TEXT,
            obs_seen_at  TEXT,
            photo_url    TEXT,
            text         TEXT NOT NULL,
            reply_markup TEXT,
            status       TEXT NOT NULL DEFAULT 'pending',
            attempts     INTEGER NOT NULL DEFAULT 0,
            created_at   TEXT NOT NULL,
            updated_at   TEXT NOT NULL,
            UNIQUE(telegram_id, notif_type, dedup_key)
        )
    """)
    for migration in [
        "ALTER TABLE favorites ADD COLUMN last_notified_at TEXT",
        "ALTER TABLE favorites ADD COLUMN last_obs_id INTEGER",
        "ALTER TABLE users ADD COLUMN season_filter INTEGER DEFAULT 0",
        "ALTER TABLE users ADD COLUMN history_initialized INTEGER DEFAULT 0",
        "ALTER TABLE rare_notifications ADD COLUMN obs_key TEXT",
        "ALTER TABLE notification_queue ADD COLUMN obs_seen_at TEXT",
    ]:
        try:
            await db.execute(migration)
        except Exception:
            pass
    # Сохраняем статус инициализации для существующих пользователей с непустой историей
    await db.execute("""
        UPDATE users SET history_initialized = 1
        WHERE history_initialized = 0
          AND telegram_id IN (SELECT DISTINCT telegram_id FROM species_history)
    """)
    await db.execute("CREATE INDEX IF NOT EXISTS idx_fav_user         ON favorites(telegram_id)")
    await db.execute("CREATE INDEX IF NOT EXISTS idx_users_alerts     ON users(alerts_enabled, lat)")
    await db.execute("CREATE INDEX IF NOT EXISTS idx_history          ON species_history(telegram_id)")
    await db.execute("CREATE INDEX IF NOT EXISTS idx_seen_rare_user   ON seen_rare_observations(telegram_id, notified_at)")
    await db.execute("CREATE INDEX IF NOT EXISTS idx_notif_queue_stat ON notification_queue(status, telegram_id)")
    await db.commit()

async def init_db():
    async with aiosqlite.connect(DB_NAME) as db:
        await _apply_schema(db)

@asynccontextmanager
async def db_transaction():
    """Единый атомарный механизм транзакций SQLite под глобальной блокировкой."""
    async with _db_lock:
        if db_conn.isolation_level is not None:
            if db_conn.in_transaction:
                await db_conn.commit()
            db_conn.isolation_level = None
        await db.execute("BEGIN IMMEDIATE") if hasattr(db_conn, "db") else await db_conn.execute("BEGIN IMMEDIATE")
        try:
            yield db_conn
        except BaseException:
            try:
                await asyncio.shield(db_conn.execute("ROLLBACK"))
            except Exception:
                pass
            raise
        else:
            await asyncio.shield(db_conn.execute("COMMIT"))

# ================= DB HELPERS =================
async def db_fetch_one(sql: str, params: tuple = ()):
    async with _db_lock:
        async with db_conn.execute(sql, params) as cur:
            return await cur.fetchone()

async def db_fetch_all(sql: str, params: tuple = ()):
    async with _db_lock:
        async with db_conn.execute(sql, params) as cur:
            return await cur.fetchall()

async def db_exec(sql: str, params: tuple = ()):
    async with db_transaction() as tx:
        await tx.execute(sql, params)

async def _upsert_user_location(uid: int, lat: float, lon: float):
    """Атомарный UPSERT координат пользователя со сбросом локальной истории и отменой старой очереди при переезде."""
    old_row = await db_fetch_one("SELECT lat, lon FROM users WHERE telegram_id = ?", (uid,))
    moved = True
    if old_row and old_row[0] is not None and old_row[1] is not None:
        moved = haversine(old_row[0], old_row[1], lat, lon) > LOCATION_RESET_DIST_KM

    now_str = datetime.now(timezone.utc).isoformat()
    async with db_transaction() as tx:
        if moved:
            await tx.execute("DELETE FROM species_history WHERE telegram_id = ?", (uid,))
            await tx.execute("DELETE FROM rare_notifications WHERE telegram_id = ?", (uid,))
            await tx.execute("DELETE FROM seen_rare_observations WHERE telegram_id = ?", (uid,))
            # Помечаем ожидающие уведомления как cancelled, чтобы не отправить текст со старым расстоянием;
            # если то же наблюдение попадёт в радиус новой локации, оно будет пересоздано с новым текстом.
            await tx.execute(
                "UPDATE notification_queue SET status = 'cancelled', updated_at = ? "
                "WHERE telegram_id = ? AND status = 'pending'",
                (now_str, uid),
            )
        await tx.execute(
            """INSERT INTO users
               (telegram_id, lat, lon, radius, period_days, alerts_enabled, season_filter, history_initialized)
               VALUES (?, ?, ?, 10, 7, 1, 0, 0)
               ON CONFLICT(telegram_id) DO UPDATE SET
                   lat = excluded.lat,
                   lon = excluded.lon,
                   history_initialized = CASE WHEN ? = 1 THEN 0 ELSE users.history_initialized END""",
            (uid, lat, lon, 1 if moved else 0),
        )

# ================= ГЕОКОДИРОВАНИЕ (NOMINATIM) =================
async def _nominatim_get(url: str, params: dict, timeout_sec: float) -> list | dict | None:
    """Глобально ограниченный по частоте запрос к Nominatim (не более 1 запроса в 1.1 с)."""
    global _nominatim_last_req_ts
    headers = {"User-Agent": "BAM-BirdsAroundMeBot/1.3.2", "Accept-Language": "ru"}
    async with _nominatim_lock:
        elapsed = time() - _nominatim_last_req_ts
        if elapsed < NOMINATIM_MIN_INTERVAL:
            await asyncio.sleep(NOMINATIM_MIN_INTERVAL - elapsed)
        try:
            async with http_session.get(
                url, params=params, headers=headers,
                timeout=aiohttp.ClientTimeout(total=timeout_sec),
            ) as r:
                _nominatim_last_req_ts = time()
                r.raise_for_status()
                return await r.json()
        except Exception as ex:
            _nominatim_last_req_ts = time()
            logger.error(f"Geocoding error [{url}]: {type(ex).__name__}: {ex}")
            return None

async def geocode_city(query: str):
    key    = query.strip().lower()
    cached = _geocode_cache.get(key)
    if cached:
        if isinstance(cached, tuple) and len(cached) == 4:
            ts, lat, lon, disp = cached
            if (time() - ts) < GEOCODE_CACHE_TTL:
                return lat, lon, disp
        elif isinstance(cached, tuple) and len(cached) == 3:
            return cached
    url    = "https://nominatim.openstreetmap.org/search"
    params = {"q": query, "format": "json", "limit": 1, "addressdetails": 1}
    data   = await _nominatim_get(url, params, timeout_sec=8)
    if data and isinstance(data, list):
        res    = data[0]
        result = (float(res["lat"]), float(res["lon"]), res.get("display_name", query))
        _geocode_cache.set(key, result)
        return result
    return None, None, None

async def reverse_geocode(lat: float, lon: float) -> str:
    key    = (round(lat, 3), round(lon, 3))
    cached = _reverse_geocode_cache.get(key)
    if cached and (time() - cached[0]) < GEOCODE_CACHE_TTL:
        return cached[1]
    url    = "https://nominatim.openstreetmap.org/reverse"
    params = {"lat": lat, "lon": lon, "format": "json", "zoom": 10, "addressdetails": 0}
    data   = await _nominatim_get(url, params, timeout_sec=6)
    if isinstance(data, dict) and data.get("display_name"):
        place = data["display_name"]
        _reverse_geocode_cache.set(key, (time(), place))
        return place
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
        dt = datetime.fromisoformat(dt_str.replace("Z", "+00:00"))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        delta = datetime.now(timezone.utc) - dt.astimezone(timezone.utc)
        return delta.days
    except Exception:
        return None

def _extract_obs_timestamp(obs: dict, fallback_iso: str) -> str:
    """Извлекает фактическое время наблюдения (time_observed_at или observed_on) в ISO UTC."""
    raw = obs.get("time_observed_at") or obs.get("observed_on")
    if not raw or not isinstance(raw, str):
        return fallback_iso
    try:
        cleaned = raw.strip().replace("Z", "+00:00")
        dt = datetime.fromisoformat(cleaned)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        else:
            dt = dt.astimezone(timezone.utc)
        now_utc = datetime.now(timezone.utc)
        if dt > now_utc:
            return now_utc.isoformat()
        return dt.isoformat()
    except Exception:
        return fallback_iso

def current_season_name() -> str:
    m = datetime.now(timezone.utc).month
    if m in (3, 4, 5):   return "🌱 весна"
    if m in (6, 7, 8):   return "☀️ лето"
    if m in (9, 10, 11): return "🍂 осень"
    return "❄️ зима"

# ================= БАЗОВЫЙ API-ЗАПРОС (iNATURALIST) =================
async def _raw_api_get(url: str, params: dict) -> dict:
    max_retries = 4
    backoff     = 1.0
    sem         = _api_semaphore or asyncio.Semaphore(API_SEMAPHORE_LIMIT)
    for attempt in range(max_retries):
        wait_time: float | None = None
        async with sem:
            try:
                async with http_session.get(
                    url, params=params, timeout=aiohttp.ClientTimeout(total=12)
                ) as r:
                    remaining = r.headers.get("X-RateLimit-Remaining")
                    if remaining is not None:
                        logger.debug(f"iNat rate limit: {remaining} remaining [{url}]")
                    if r.status == 429:
                        ra = (r.headers.get("Retry-After") or "").strip()
                        try:
                            wait_time = min(float(ra), 60.0) if ra else backoff
                        except ValueError:
                            wait_time = backoff
                        logger.warning(f"429 от iNaturalist — жду {wait_time}s (попытка {attempt + 1})")
                        backoff *= 2
                    elif 500 <= r.status < 600:
                        wait_time = backoff
                        logger.warning(f"HTTP {r.status} от iNaturalist [{url}] — жду {wait_time}s (попытка {attempt + 1})")
                        backoff *= 2
                    elif 400 <= r.status < 500:
                        logger.warning(f"HTTP {r.status} клиентская ошибка [{url}]")
                        return {}
                    else:
                        r.raise_for_status()
                        data = await r.json()
                        return data if isinstance(data, dict) else {}
            except (aiohttp.ClientResponseError, aiohttp.ClientConnectorError,
                    aiohttp.ClientError, asyncio.TimeoutError) as ex:
                logger.warning(f"API transient error [{url}] попытка {attempt + 1}: {type(ex).__name__}: {ex}")
                wait_time = backoff
                backoff *= 2
            except Exception as ex:
                logger.exception(f"Неожиданная ошибка [{url}]: {type(ex).__name__}")
                break

        # Ожидание выполняется строго ВНЕ семафора и контекста HTTP-ответа
        if wait_time is not None and attempt + 1 < max_retries:
            await asyncio.sleep(wait_time)

    logger.error(f"API запрос не удался [{url}] после {max_retries} попыток")
    return {}

async def api_get(url: str, params: dict) -> dict:
    return await _raw_api_get(url, params)

# ================= EBIRD API =================
async def _ebird_get_with_status(endpoint: str, params: dict) -> tuple[list, bool]:
    """Запрос к eBird API с отдельным семафором и обработкой 429/5xx.
    Возвращает кортеж (results, had_error) без использования глобальных флагов.
    """
    if not EBIRD_API_KEY:
        return [], False
    url         = f"{EBIRD_BASE}{endpoint}"
    headers     = {"X-eBirdApiToken": EBIRD_API_KEY}
    max_retries = 3
    backoff     = 1.0
    sem         = _ebird_semaphore or asyncio.Semaphore(EBIRD_SEMAPHORE_LIMIT)
    for attempt in range(max_retries):
        wait_time: float | None = None
        async with sem:
            try:
                async with http_session.get(
                    url, params=params, headers=headers,
                    timeout=aiohttp.ClientTimeout(total=10),
                ) as r:
                    if r.status == 429:
                        ra = (r.headers.get("Retry-After") or "").strip()
                        try:
                            wait_time = min(float(ra), 60.0) if ra else backoff
                        except ValueError:
                            wait_time = backoff
                        logger.warning(f"eBird rate limit hit — жду {wait_time}s (попытка {attempt + 1})")
                        backoff *= 2
                    elif 500 <= r.status < 600:
                        wait_time = backoff
                        logger.warning(f"eBird HTTP {r.status} [{endpoint}] (попытка {attempt + 1})")
                        backoff *= 2
                    elif 400 <= r.status < 500:
                        logger.warning(f"eBird HTTP {r.status} [{endpoint}]")
                        return [], True
                    else:
                        r.raise_for_status()
                        data = await r.json()
                        return (data if isinstance(data, list) else []), False
            except (aiohttp.ClientError, asyncio.TimeoutError) as ex:
                logger.warning(f"eBird API error [{endpoint}] попытка {attempt + 1}: {type(ex).__name__}: {ex}")
                wait_time = backoff
                backoff *= 2
            except Exception as ex:
                logger.warning(f"eBird unexpected error [{endpoint}]: {type(ex).__name__}")
                return [], True

        if wait_time is not None and attempt + 1 < max_retries:
            await asyncio.sleep(wait_time)

    return [], True

async def _ebird_get(endpoint: str, params: dict) -> list:
    """Запрос к eBird API. Возвращает [] при отсутствии ключа или ошибке."""
    results, _ = await _ebird_get_with_status(endpoint, params)
    return results

async def get_ebird_notable(lat: float, lon: float, dist: int = 25, back: int = 14) -> list:
    """Редкие/необычные наблюдения поблизости по данным eBird (curated reviewers)."""
    if not EBIRD_API_KEY:
        return []
    key   = (round(lat, 2), round(lon, 2), dist)
    entry = _ebird_notable_cache.get(key)
    if entry and (time() - entry[0]) < EBIRD_NOTABLE_TTL:
        return entry[1]
    results, had_error = await _ebird_get_with_status("/data/obs/geo/recent/notable", {
        "lat": round(lat, 4), "lng": round(lon, 4),
        "dist": min(dist, 50), "back": min(back, 30),
        "detail": "simple", "hotspot": "false",
    })
    if not had_error:
        _ebird_notable_cache.set(key, (time(), results))
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
    if "results" not in data:
        return []
    results = data["results"]
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
    if "results" in data:
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
    data = await api_get(f"{API_BASE}/taxa", {
        "q": query, "iconic_taxa": "Aves", "locale": "ru", "per_page": 8,
    })
    if "results" not in data:
        return []
    results = data["results"]
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
            obs_lat, obs_lon = _parse_obs_coords(obs)
            if obs_lat is not None and haversine(lat, lon, obs_lat, obs_lon) <= radius:
                latest[tid] = obs
    return latest

# ================= ОПРЕДЕЛЕНИЕ ПТИЦЫ ПО ФОТО =================
_BIRD_ICONIC_NAMES = {"Aves"}

async def identify_bird_photo(photo_bytes: bytes, lat: float = None, lon: float = None) -> list:
    """Отправляет фото в iNaturalist CV API.
    Поле называется 'image' (не 'file') — ключевое отличие от обычного upload.
    Возвращает топ-5 результатов; птиц выбираем по iconic_taxon_name или ancestor_ids.
    """
    try:
        form = aiohttp.FormData()
        form.add_field("image", photo_bytes, filename="photo.jpg", content_type="image/jpeg")
        if lat is not None and lon is not None:
            form.add_field("lat", str(round(lat, 4)))
            form.add_field("lng", str(round(lon, 4)))

        sem = _api_semaphore or asyncio.Semaphore(API_SEMAPHORE_LIMIT)
        async with sem:
            async with http_session.post(
                f"{API_BASE}/computervision/score_image",
                data=form,
                timeout=aiohttp.ClientTimeout(total=40),
            ) as r:
                body = await r.text()
                if r.status != 200:
                    logger.error(f"CV API HTTP {r.status}: {body[:300]}")
                    return []
                data = await r.json(content_type=None)

        all_results = data.get("results", [])
        logger.info(f"CV API returned {len(all_results)} results")

        birds = []
        other = []
        for item in all_results:
            t = item.get("taxon", {})
            iconic = t.get("iconic_taxon_name", "")
            ancestors = t.get("ancestor_ids", [])
            if iconic in _BIRD_ICONIC_NAMES or 3 in ancestors:
                birds.append(item)
            else:
                other.append(item)

        result = birds if birds else all_results
        return result[:5]

    except Exception as ex:
        logger.error(f"CV API error: {type(ex).__name__}: {ex}", exc_info=True)
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
    return flags

_IUCN_STATUS_LABELS: dict[str, str] = {
    "cr": "CR — на грани исчезновения",
    "en": "EN — исчезающий вид",
    "vu": "VU — уязвимый вид",
    "nt": "NT — близкий к уязвимому",
    "lc": "LC — вне угрозы",
    "dd": "DD — недостаточно данных",
    "ex": "EX — вымерший",
    "ew": "EW — вымерший в дикой природе",
}

def _conservation_label(cs: dict) -> str:
    """Возвращает строку вида 'CR — на грани исчезновения' из dict conservation_status."""
    code = cs.get("status", "").lower()
    return _IUCN_STATUS_LABELS.get(code, code.upper() if code else "")

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
    cs_dict       = {}
    if taxon_data and taxon_data.get("results"):
        t             = taxon_data["results"][0]
        cs_dict       = (t.get("conservation_status") or {})
        is_threatened = cs_dict.get("status", "").lower() in ("cr", "en", "vu")
        global_count  = t.get("observations_count", 0)

    if is_threatened:
        status_label   = _conservation_label(cs_dict)
        rare_emoji     = "🔴"
        rare_label     = f"Охраняемый вид · {status_label}" if status_label else "Охраняемый вид"
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

# ================= ФОТО, ЭКРАНИРОВАНИЕ И ОТПРАВКА КАРТОЧЕК =================
def get_photo_url(obs: dict, size: str = "medium") -> str | None:
    if obs.get("photos"):
        return obs["photos"][0]["url"].replace("square", size)
    return None

def e(text: str) -> str:
    return html_module.escape(str(text))

def _is_user_blocked_error(ex: BaseException) -> bool:
    if isinstance(ex, TelegramForbiddenError):
        return True
    msg = str(ex).lower()
    return any(
        marker in msg
        for marker in (
            "forbidden",
            "bot was blocked by the user",
            "user is deactivated",
            "chat not found",
            "bot can't initiate conversation",
        )
    )

async def _disable_user_alerts(telegram_id: int):
    try:
        await db_exec(
            """INSERT INTO users (telegram_id, lat, lon, radius, period_days, alerts_enabled, season_filter)
               VALUES (?, NULL, NULL, 10, 7, 0, 0)
               ON CONFLICT(telegram_id) DO UPDATE SET alerts_enabled = 0""",
            (telegram_id,),
        )
        logger.info(f"Уведомления отключены для заблокировавшего пользователя {telegram_id}")
    except Exception:
        logger.error(f"Не удалось отключить уведомления для {telegram_id}", exc_info=True)

async def safe_send_card(
    telegram_id: int,
    photo_url: str | None,
    text: str,
    reply_markup: InlineKeyboardMarkup | None = None,
) -> str:
    """Единый надёжный механизм отправки карточки (fallback send_photo -> send_message).
    Возвращает статус: 'sent' | 'blocked' | 'transient_error' | 'failed'.
    """
    sem = _tg_send_semaphore or asyncio.Semaphore(TG_SEND_SEMAPHORE_LIMIT)

    async def _call_tg(coro_factory):
        for attempt in range(2):
            wait_sec = None
            async with sem:
                try:
                    await coro_factory()
                    return "sent"
                except TelegramRetryAfter as ex:
                    wait_sec = min(float(getattr(ex, "retry_after", 5.0)), 30.0)
                    logger.warning(f"Telegram RetryAfter {wait_sec}s для user {telegram_id}")
                except Exception as ex:
                    if _is_user_blocked_error(ex):
                        await _disable_user_alerts(telegram_id)
                        return "blocked"
                    raise
            if wait_sec is not None and attempt == 0:
                await asyncio.sleep(wait_sec)
        return "transient_error"

    if photo_url:
        try:
            res = await _call_tg(
                lambda: bot.send_photo(
                    telegram_id, photo_url, caption=text,
                    reply_markup=reply_markup, parse_mode="HTML",
                )
            )
            if res in ("sent", "blocked"):
                return res
        except Exception as ex:
            logger.warning(
                f"Ошибка send_photo для user {telegram_id} ({type(ex).__name__}: {ex}) — fallback на send_message"
            )

    try:
        return await _call_tg(
            lambda: bot.send_message(
                telegram_id, text, reply_markup=reply_markup, parse_mode="HTML",
            )
        )
    except (TelegramNetworkError, TelegramServerError, aiohttp.ClientError, asyncio.TimeoutError) as ex:
        logger.error(f"Временная ошибка Telegram для user {telegram_id}: {type(ex).__name__}: {ex}")
        return "transient_error"
    except TelegramBadRequest as ex:
        logger.error(f"Ошибка TelegramBadRequest для user {telegram_id}: {ex}")
        return "failed"
    except Exception as ex:
        logger.error(f"Неожиданная ошибка отправки для user {telegram_id}: {type(ex).__name__}: {ex}")
        return "transient_error"

def _serialize_kb(kb: InlineKeyboardMarkup | None) -> str | None:
    if kb is None:
        return None
    rows = []
    for row in kb.inline_keyboard:
        rows.append([
            {
                k: v for k, v in {
                    "text": btn.text,
                    "url": getattr(btn, "url", None),
                    "callback_data": getattr(btn, "callback_data", None),
                }.items() if v is not None
            }
            for btn in row
        ])
    return json.dumps(rows, ensure_ascii=False)

def _deserialize_kb(kb_json: str | None) -> InlineKeyboardMarkup | None:
    if not kb_json:
        return None
    try:
        rows = json.loads(kb_json)
        return InlineKeyboardMarkup(
            inline_keyboard=[
                [InlineKeyboardButton(**btn_dict) for btn_dict in row]
                for row in rows
            ]
        )
    except Exception:
        return None

def _ebird_taxon_hash(key_str: str) -> int:
    """Детерминированный отрицательный ID таксона для записи eBird в rare_notifications."""
    digest = hashlib.sha256(key_str.encode("utf-8")).digest()
    return -int.from_bytes(digest[:6], "big")

def _ebird_obs_key(notable: dict) -> str:
    obs_id = notable.get("obsId")
    if obs_id:
        return f"ebird:{obs_id}"
    sub_id  = notable.get("subId") or ""
    sp_code = (notable.get("speciesCode") or notable.get("sciName") or notable.get("comName") or "").lower()
    obs_dt  = notable.get("obsDt") or ""
    loc_id  = notable.get("locId") or ""
    return f"ebird:{sub_id}:{sp_code}:{obs_dt}:{loc_id}"

async def _apply_notification_state_tx(
    tx: aiosqlite.Connection,
    telegram_id: int,
    notif_type: str,
    dedup_key: str,
    taxon_id: int | None,
    obs_id: str | None,
    sci_name: str | None,
    now_str: str,
    obs_seen_at: str | None = None,
):
    if notif_type == "rare_inat":
        if taxon_id is not None:
            await tx.execute(
                """INSERT OR REPLACE INTO rare_notifications
                   (telegram_id, taxon_id, notified_at, obs_key)
                   VALUES (?, ?, ?, ?)""",
                (telegram_id, taxon_id, now_str, dedup_key),
            )
        await tx.execute(
            """INSERT OR REPLACE INTO seen_rare_observations
               (telegram_id, obs_key, taxon_key, sci_name, notified_at)
               VALUES (?, ?, ?, ?, ?)""",
            (telegram_id, dedup_key, f"inat:{taxon_id}", (sci_name or "").lower(), now_str),
        )
    elif notif_type == "rare_ebird":
        neg_tid = taxon_id if taxon_id is not None else _ebird_taxon_hash(sci_name or dedup_key)
        await tx.execute(
            """INSERT OR REPLACE INTO rare_notifications
               (telegram_id, taxon_id, notified_at, obs_key)
               VALUES (?, ?, ?, ?)""",
            (telegram_id, neg_tid, now_str, dedup_key),
        )
        await tx.execute(
            """INSERT OR REPLACE INTO seen_rare_observations
               (telegram_id, obs_key, taxon_key, sci_name, notified_at)
               VALUES (?, ?, ?, ?, ?)""",
            (telegram_id, dedup_key, f"ebird:{neg_tid}", (sci_name or "").lower(), now_str),
        )
    elif notif_type == "wishlist":
        obs_int = int(obs_id) if (obs_id and str(obs_id).isdigit()) else None
        await tx.execute(
            """UPDATE favorites
               SET last_notified_at = ?, last_obs_id = COALESCE(?, last_obs_id)
               WHERE telegram_id = ? AND taxon_id = ?""",
            (now_str, obs_int, telegram_id, taxon_id),
        )
    elif notif_type == "bird_alert":
        if taxon_id is not None:
            seen_ts = obs_seen_at or now_str
            await tx.execute(
                """INSERT INTO species_history (telegram_id, taxon_id, last_seen_at)
                   VALUES (?, ?, ?)
                   ON CONFLICT(telegram_id, taxon_id)
                   DO UPDATE SET last_seen_at = CASE
                       WHEN excluded.last_seen_at > species_history.last_seen_at
                       THEN excluded.last_seen_at
                       ELSE species_history.last_seen_at
                   END""",
                (telegram_id, taxon_id, seen_ts),
            )

async def _enqueue_notification(
    telegram_id: int,
    notif_type: str,
    dedup_key: str,
    taxon_id: int | None,
    obs_id: str | None,
    sci_name: str | None,
    photo_url: str | None,
    text: str,
    kb: InlineKeyboardMarkup | None,
    now_str: str,
    obs_seen_at: str | None = None,
) -> tuple[int, str]:
    """Создаёт или актуализирует запись в очереди уведомлений.
    Если прежняя запись была отменена при смене локации ('cancelled') или ожидает ('pending'),
    обновляет её новым текстом, фото и кнопками для текущих координат и переводит в 'pending'.
    """
    kb_json = _serialize_kb(kb)
    obs_id_str = str(obs_id) if obs_id is not None else None
    async with db_transaction() as tx:
        async with tx.execute(
            """SELECT id, status, attempts FROM notification_queue
               WHERE telegram_id = ? AND notif_type = ? AND dedup_key = ?""",
            (telegram_id, notif_type, dedup_key),
        ) as cur:
            existing = await cur.fetchone()

        if existing:
            q_id, q_status, q_attempts = existing[0], existing[1], existing[2]
            if q_status == "sent":
                return q_id, "sent"
            if q_status == "failed" and q_attempts >= 3:
                return q_id, "failed"
            # Если запись была отменена ('cancelled') из-за смены локации или 'failed' (<3 попыток),
            # либо 'pending' — обновляем карточку актуальным текстом/расстоянием и возвращаем 'pending'.
            reset_attempts = 0 if q_status in ("cancelled", "failed") else q_attempts
            await tx.execute(
                """UPDATE notification_queue
                   SET taxon_id = ?, obs_id = ?, sci_name = ?, obs_seen_at = ?,
                       photo_url = ?, text = ?, reply_markup = ?,
                       status = 'pending', attempts = ?, updated_at = ?
                   WHERE id = ?""",
                (
                    taxon_id, obs_id_str, sci_name, obs_seen_at,
                    photo_url, text, kb_json,
                    reset_attempts, now_str, q_id,
                ),
            )
            return q_id, "pending"

        async with tx.execute(
            """INSERT INTO notification_queue
               (telegram_id, notif_type, dedup_key, taxon_id, obs_id, sci_name, obs_seen_at,
                photo_url, text, reply_markup, status, attempts, created_at, updated_at)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'pending', 0, ?, ?)""",
            (
                telegram_id, notif_type, dedup_key, taxon_id,
                obs_id_str, sci_name, obs_seen_at,
                photo_url, text, kb_json, now_str, now_str,
            ),
        ) as cur:
            return cur.lastrowid, "pending"

async def _deliver_queued_notification(q_id: int, now_str: str | None = None) -> tuple[bool, str]:
    """Доставляет уведомление из очереди ТОЛЬКО если его актуальный статус равен 'pending'."""
    now_str = now_str or datetime.now(timezone.utc).isoformat()
    row = await db_fetch_one(
        """SELECT id, telegram_id, notif_type, dedup_key, taxon_id, obs_id,
                  sci_name, obs_seen_at, photo_url, text, reply_markup, status, attempts
           FROM notification_queue WHERE id = ?""",
        (q_id,),
    )
    if not row:
        return False, "not_found"

    (
        _, uid, n_type, d_key, tid, obs_id,
        sci_name, obs_seen_at, photo_url, text, kb_json, status, attempts
    ) = (
        row[0], row[1], row[2], row[3], row[4], row[5],
        row[6], row[7], row[8], row[9], row[10], row[11], row[12]
    )

    if status != "pending":
        return False, status
    if attempts >= 3:
        await db_exec(
            "UPDATE notification_queue SET status = 'failed', updated_at = ? WHERE id = ? AND status = 'pending'",
            (now_str, q_id),
        )
        return False, "failed"

    u_row = await db_fetch_one("SELECT alerts_enabled FROM users WHERE telegram_id = ?", (uid,))
    if u_row and u_row[0] == 0:
        await db_exec(
            "UPDATE notification_queue SET status = 'cancelled', updated_at = ? WHERE id = ? AND status = 'pending'",
            (now_str, q_id),
        )
        return False, "cancelled"

    kb = _deserialize_kb(kb_json)
    send_status = await safe_send_card(uid, photo_url, text, kb)

    async with db_transaction() as tx:
        # Повторно проверяем, не была ли запись отменена (например, сменой города) во время сетевой отправки
        async with tx.execute("SELECT status FROM notification_queue WHERE id = ?", (q_id,)) as cur:
            cur_row = await cur.fetchone()
        current_status = cur_row[0] if cur_row else None

        if send_status == "sent":
            await tx.execute(
                """UPDATE notification_queue
                   SET status = 'sent', attempts = attempts + 1, updated_at = ?
                   WHERE id = ?""",
                (now_str, q_id),
            )
            if current_status == "pending":
                await _apply_notification_state_tx(
                    tx, uid, n_type, d_key, tid, obs_id, sci_name, now_str, obs_seen_at=obs_seen_at
                )
            return True, "sent"
        elif send_status in ("blocked", "failed"):
            await tx.execute(
                """UPDATE notification_queue
                   SET status = 'failed', attempts = attempts + 1, updated_at = ?
                   WHERE id = ? AND status = 'pending'""",
                (now_str, q_id),
            )
            return False, send_status
        else:
            await tx.execute(
                """UPDATE notification_queue
                   SET attempts = attempts + 1,
                       status = CASE WHEN attempts + 1 >= 3 THEN 'failed' ELSE 'pending' END,
                       updated_at = ?
                   WHERE id = ? AND status = 'pending'""",
                (now_str, q_id),
            )
            return False, "transient_error"

async def _enqueue_and_deliver_notification(
    telegram_id: int,
    notif_type: str,
    dedup_key: str,
    taxon_id: int | None,
    obs_id: str | None,
    sci_name: str | None,
    photo_url: str | None,
    text: str,
    kb: InlineKeyboardMarkup | None,
    now_str: str,
    obs_seen_at: str | None = None,
) -> tuple[bool, str]:
    """Постановка уведомления в очередь и немедленная доставка (только для статуса 'pending')."""
    q_id, q_status = await _enqueue_notification(
        telegram_id=telegram_id,
        notif_type=notif_type,
        dedup_key=dedup_key,
        taxon_id=taxon_id,
        obs_id=obs_id,
        sci_name=sci_name,
        photo_url=photo_url,
        text=text,
        kb=kb,
        now_str=now_str,
        obs_seen_at=obs_seen_at,
    )
    if q_status != "pending":
        return False, q_status
    return await _deliver_queued_notification(q_id, now_str=now_str)

async def process_pending_notifications():
    """Восстановление и досылка строго ожидающих уведомлений (status = 'pending') после перезапуска или сбоя."""
    rows = await db_fetch_all(
        """SELECT id FROM notification_queue
           WHERE status = 'pending' AND attempts < 3
           ORDER BY id ASC"""
    )
    if not rows:
        return
    logger.info(f"process_pending_notifications: найдено {len(rows)} незавершённых уведомлений")
    now_str = datetime.now(timezone.utc).isoformat()
    for row in rows:
        await _deliver_queued_notification(row[0], now_str=now_str)

# ================= КЛАВИАТУРА =================
async def main_keyboard(user_id: int) -> ReplyKeyboardMarkup:
    if user_id not in _fav_count_cache:
        rows = await db_fetch_all(
            "SELECT COUNT(*) FROM favorites WHERE telegram_id = ?", (user_id,)
        )
        _fav_count_cache[user_id] = rows[0][0] if rows else 0
    fav_count = _fav_count_cache[user_id]
    fav_label = f"⭐ Вишлист ({fav_count})" if fav_count else "⭐ Вишлист"
    kb = [
        [KeyboardButton(text="🐦 Сканировать"), KeyboardButton(text="📷 Определить птицу")],
        [KeyboardButton(text="🚨 Редкие птицы"), KeyboardButton(text=fav_label)],
        [KeyboardButton(text="⚙️ Настройки")],
    ]
    return ReplyKeyboardMarkup(keyboard=kb, resize_keyboard=True)

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
        (telegram_id, lat, lon, radius, period_days, alerts_enabled, season_filter, history_initialized)
        VALUES (?, NULL, NULL, 10, 7, 1, 0, 0)
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
    await message.answer(
        "🐦 <b>BAM – Birds Around Me</b>\n\n"
        "<b>Кнопки:</b>\n"
        "🐦 Сканировать — список птиц в радиусе\n"
        "📷 Определить птицу — пришлите фото, бот определит вид\n"
        "🚨 Редкие птицы — охраняемые и необычные виды рядом\n"
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
    uid = message.from_user.id
    await state.clear()
    lat = message.location.latitude
    lon = message.location.longitude
    await _upsert_user_location(uid, lat, lon)
    _invalidate_scan_cache(uid)
    place = await reverse_geocode(lat, lon)
    await message.answer(
        f"✅ <b>Геолокация сохранена!</b>\n\n📍 {e(place)}\n\n"
        f"Теперь можно сканировать или вернуться в <b>⚙️ Настройки</b>.",
        reply_markup=await main_keyboard(uid),
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

@router.message(F.text == "❌ Отмена")
async def cancel_location_request(message: Message, state: FSMContext):
    await state.clear()
    await message.answer(
        "Отменено.",
        reply_markup=await main_keyboard(message.from_user.id),
    )

@router.message(Form.waiting_city)
async def handle_city_input(message: Message, state: FSMContext):
    if not message.from_user or not message.text:
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
    await _upsert_user_location(uid, lat, lon)
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

    row = await db_fetch_one("SELECT lat, lon FROM users WHERE telegram_id = ?", (uid,))
    lat, lon = (row[0], row[1]) if row and row[0] is not None else (None, None)

    photo = message.photo[-1]
    try:
        buf = io.BytesIO()
        await bot.download(photo, destination=buf)
        photo_bytes = buf.getvalue()
        if not photo_bytes:
            raise ValueError("Пустой буфер изображения")
    except Exception as ex:
        try:
            await wait_ms.delete()
        except Exception:
            pass
        logger.error(f"Ошибка загрузки фото (file_id={photo.file_id}): {type(ex).__name__}")
        await message.answer("❌ Не удалось загрузить фото. Попробуйте ещё раз.")
        return

    results = await identify_bird_photo(photo_bytes, lat, lon)
    try:
        await wait_ms.delete()
    except Exception:
        pass

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

    first_tid = results[0].get("taxon", {}).get("id")
    if first_tid:
        kb_rows.append([InlineKeyboardButton(
            text="🐦 Открыть карточку первого вида",
            callback_data=f"bird:{first_tid}:0",
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
    if not row or row[0] is None:
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

    if not row or row[0] is None:
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
    await safe_send_card(callback.from_user.id, photo_medium, text, kb)
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
        text += f"• {e(name)}\n"
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

    kb = InlineKeyboardMarkup(inline_keyboard=[
        # --- Местоположение ---
        [InlineKeyboardButton(text="── 🌍 Местоположение ──", callback_data="noop")],
        [InlineKeyboardButton(text="🏠 Ввести город",           callback_data="set_city"),
         InlineKeyboardButton(text="📍 Геолокация",       callback_data="set_location_request")],
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
    uid = callback.from_user.id
    row = await db_fetch_one(
        "SELECT radius, period_days, alerts_enabled, season_filter, lat, lon FROM users WHERE telegram_id = ?",
        (uid,),
    ) or (10, 7, 1, 0, None, None)
    r, d, current_alerts, season, lat, lon = row
    new_val = 0 if current_alerts else 1
    await db_exec(
        """INSERT INTO users (telegram_id, lat, lon, radius, period_days, alerts_enabled, season_filter)
           VALUES (?, NULL, NULL, 10, 7, ?, 0)
           ON CONFLICT(telegram_id) DO UPDATE SET alerts_enabled = excluded.alerts_enabled""",
        (uid, new_val),
    )
    location_name = await reverse_geocode(lat, lon) if lat is not None and lon is not None else ""
    text, kb = _build_settings_content(r, d, new_val, season, location_name)
    try:
        await callback.message.edit_text(text, parse_mode="HTML", reply_markup=kb)
    except Exception:
        pass
    label = "включены ✅" if new_val else "выключены ❌"
    await callback.answer(f"🔔 Уведомления {label}", show_alert=False)

@router.callback_query(F.data == "toggle_season")
async def toggle_season(callback: CallbackQuery):
    uid = callback.from_user.id
    row = await db_fetch_one(
        "SELECT radius, period_days, alerts_enabled, season_filter, lat, lon FROM users WHERE telegram_id = ?",
        (uid,),
    ) or (10, 7, 1, 0, None, None)
    r, d, alerts, current_season, lat, lon = row
    new_season = 0 if current_season else 1
    await db_exec(
        """INSERT INTO users (telegram_id, lat, lon, radius, period_days, alerts_enabled, season_filter)
           VALUES (?, NULL, NULL, 10, 7, 1, ?)
           ON CONFLICT(telegram_id) DO UPDATE SET season_filter = excluded.season_filter""",
        (uid, new_season),
    )
    _invalidate_scan_cache(uid)
    location_name = await reverse_geocode(lat, lon) if lat is not None and lon is not None else ""
    text, kb = _build_settings_content(r, d, alerts, new_season, location_name)
    try:
        await callback.message.edit_text(text, parse_mode="HTML", reply_markup=kb)
    except Exception:
        pass
    label = f"включён ({current_season_name()})" if new_season else "выключен"
    await callback.answer(f"🌿 Сезонный фильтр {label}", show_alert=False)

@router.callback_query(F.data.startswith("set_r:"))
async def set_radius(callback: CallbackQuery, state: FSMContext):
    uid   = callback.from_user.id
    value = callback.data.split(":")[1]
    if value == "custom":
        await state.set_state(Form.waiting_custom_radius)
        await callback.message.answer(
            "✏️ Введите радиус в километрах (1–200):\n\nНапример: <b>42</b>\n\nИли /cancel",
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
    await db_exec(
        """INSERT INTO users (telegram_id, lat, lon, radius, period_days, alerts_enabled, season_filter)
           VALUES (?, NULL, NULL, ?, 7, 1, 0)
           ON CONFLICT(telegram_id) DO UPDATE SET radius = excluded.radius""",
        (uid, r),
    )
    _invalidate_scan_cache(uid)
    row = await db_fetch_one(
        "SELECT radius, period_days, alerts_enabled, season_filter, lat, lon FROM users WHERE telegram_id = ?",
        (uid,),
    ) or (r, 7, 1, 0, None, None)
    _r, d, alerts, season, lat, lon = row
    location_name = await reverse_geocode(lat, lon) if lat is not None and lon is not None else ""
    text, kb = _build_settings_content(_r, d, alerts, season, location_name)
    try:
        await callback.message.edit_text(text, parse_mode="HTML", reply_markup=kb)
    except Exception:
        pass
    await callback.answer(f"✅ Радиус: {r} км", show_alert=False)

@router.message(Form.waiting_custom_radius)
async def handle_custom_radius(message: Message, state: FSMContext):
    if not message.from_user or not message.text:
        return
    uid = message.from_user.id
    try:
        r = int(message.text.strip())
        if not 1 <= r <= 200:
            raise ValueError
    except ValueError:
        await message.answer("❌ Введите целое число от 1 до 200:")
        return
    await db_exec(
        """INSERT INTO users (telegram_id, lat, lon, radius, period_days, alerts_enabled, season_filter)
           VALUES (?, NULL, NULL, ?, 7, 1, 0)
           ON CONFLICT(telegram_id) DO UPDATE SET radius = excluded.radius""",
        (uid, r),
    )
    _invalidate_scan_cache(uid)
    await state.clear()
    await message.answer(f"✅ Радиус установлен: {r} км",
                         reply_markup=await main_keyboard(uid))

@router.callback_query(F.data.startswith("set_d:"))
async def set_days(callback: CallbackQuery):
    uid = callback.from_user.id
    d   = int(callback.data.split(":")[1])
    await db_exec(
        """INSERT INTO users (telegram_id, lat, lon, radius, period_days, alerts_enabled, season_filter)
           VALUES (?, NULL, NULL, 10, ?, 1, 0)
           ON CONFLICT(telegram_id) DO UPDATE SET period_days = excluded.period_days""",
        (uid, d),
    )
    _invalidate_scan_cache(uid)
    row = await db_fetch_one(
        "SELECT radius, period_days, alerts_enabled, season_filter, lat, lon FROM users WHERE telegram_id = ?",
        (uid,),
    ) or (10, d, 1, 0, None, None)
    r, _d, alerts, season, lat, lon = row
    location_name = await reverse_geocode(lat, lon) if lat is not None and lon is not None else ""
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
        "SELECT lat, lon, radius, period_days, alerts_enabled FROM users WHERE telegram_id = ?",
        (telegram_id,)
    )
    if not row or row[0] is None:
        if manual:
            await bot.send_message(telegram_id, "❌ Сначала укажи город!")
        return

    lat, lon, radius, days, alerts_enabled = row
    if not manual and not alerts_enabled:
        return

    # iNaturalist-наблюдения
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

    # eBird notable birds
    ebird_notables = []
    if EBIRD_API_KEY:
        ebird_notables = await get_ebird_notable(lat, lon, dist=min(radius, 50))

    if not observations and not ebird_notables:
        if manual:
            await bot.send_message(telegram_id, "✅ Пока нет редких птиц в вашем радиусе.")
        return

    # Постоянная дедупликация для авто-режима (по таксонам за 24ч и по ID наблюдений)
    recent_notified: set[int]   = set()
    notified_obs_keys: set[str] = set()
    shown_names: set[str]       = set()
    shown_sci_names: set[str]   = set()

    if not manual:
        rows = await db_fetch_all(
            "SELECT taxon_id, obs_key FROM rare_notifications "
            "WHERE telegram_id = ? AND notified_at > datetime('now', '-24 hours')",
            (telegram_id,),
        )
        for r in rows:
            recent_notified.add(r[0])
            if r[1]:
                notified_obs_keys.add(r[1])

        obs_rows = await db_fetch_all(
            "SELECT obs_key, sci_name, notified_at FROM seen_rare_observations WHERE telegram_id = ?",
            (telegram_id,),
        )
        for r in obs_rows:
            notified_obs_keys.add(r[0])
            if r[1] and (days_since(r[2]) or 0) < 1:
                shown_sci_names.add(r[1].strip().lower())

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

        taxon_inline  = obs.get("taxon", {})
        cs            = (taxon_inline.get("conservation_status") or {})
        status_code   = cs.get("status", "").lower()
        is_threatened = status_code in ("cr", "en", "vu") or bool(taxon_inline.get("threatened"))
        global_count  = taxon_inline.get("observations_count", 0)

        if not is_threatened and global_count > RARITY_GLOBAL_COMMON_THRESHOLD:
            continue

        obs_key = f"inat:{obs.get('id', tid)}"
        if not manual:
            taxon_cached = _get_taxon_cached(tid)
            if taxon_cached and taxon_cached.get("results"):
                cs_cached = (taxon_cached["results"][0].get("conservation_status") or {})
                if cs_cached.get("status", "").lower() not in ("cr", "en", "vu"):
                    continue
            else:
                if not is_threatened:
                    continue
            if tid in recent_notified or obs_key in notified_obs_keys:
                if taxon_inline.get("name"):
                    shown_sci_names.add(taxon_inline["name"].strip().lower())
                continue

        if is_threatened:
            cs_inline   = (obs.get("taxon", {}).get("conservation_status") or {})
            status_lbl  = _conservation_label(cs_inline)
            rarity_line = f"🔴 Охраняемый вид · {status_lbl}" if status_lbl else "🔴 Охраняемый вид"
        elif global_count <= RARITY_LOCAL_RARE_THRESHOLD:
            rarity_line = "🔴 Очень редко встречается"
        else:
            rarity_line = "🟡 Редко встречается в этом районе"

        taxon_obj = obs["taxon"]
        name      = taxon_obj.get("preferred_common_name") or taxon_obj["name"]
        sci       = taxon_obj.get("name", "")
        ago       = time_ago(obs.get("time_observed_at") or obs.get("observed_on"))
        photo_med = get_photo_url(obs, "medium")
        photo_ori = get_photo_url(obs, "original")
        url       = f"https://www.inaturalist.org/observations/{obs['id']}"

        taxon_cached_data = _get_taxon_cached(tid)
        family_name, order_name = _extract_taxonomy(taxon_cached_data) if taxon_cached_data else ("", "")
        taxonomy_str = ""
        if order_name or family_name:
            taxonomy_str = "🔬 " + " · ".join(filter(None, [e(order_name), e(family_name)])) + "\n"

        text = (
            f"🚨 <b>{e(name)}</b>  <i>{e(sci)}</i>\n"
            f"{taxonomy_str}"
            f"\n{rarity_line}\n"
            f"📍 {dist} км от вас\n"
            f"🕒 {ago}\n"
            f"\n<i>Редкое наблюдение рядом · iNaturalist</i>"
        )
        kb_rows = [[InlineKeyboardButton(text="Открыть на iNaturalist →", url=url)]]
        if photo_ori:
            kb_rows.append([InlineKeyboardButton(text="🔍 Фото в полном размере", url=photo_ori)])
        kb = InlineKeyboardMarkup(inline_keyboard=kb_rows)

        if manual:
            send_res = await safe_send_card(telegram_id, photo_med, text, kb)
            if send_res == "blocked":
                return
            found_any = True
            shown_names.add(name.strip().lower())
            if sci:
                shown_sci_names.add(sci.strip().lower())
        else:
            delivered, status = await _enqueue_and_deliver_notification(
                telegram_id=telegram_id,
                notif_type="rare_inat",
                dedup_key=obs_key,
                taxon_id=tid,
                obs_id=str(obs.get("id", "")),
                sci_name=sci,
                photo_url=photo_med,
                text=text,
                kb=kb,
                now_str=now_str,
            )
            if status == "blocked":
                return
            if delivered:
                found_any = True
                sent_count += 1
                recent_notified.add(tid)
                notified_obs_keys.add(obs_key)
                shown_names.add(name.strip().lower())
                if sci:
                    shown_sci_names.add(sci.strip().lower())

    # --- eBird notable birds ---
    if ebird_notables and (manual or sent_count < 3):
        sent_ebird = 0
        for notable in ebird_notables:
            if not manual and (sent_count + sent_ebird) >= 3:
                break

            com_name = (notable.get("comName") or "").strip()
            sci_name = (notable.get("sciName") or "").strip()
            if not com_name:
                continue
            if com_name.lower() in shown_names:
                continue
            if sci_name and sci_name.lower() in shown_sci_names:
                continue

            nb_lat = notable.get("lat")
            nb_lon = notable.get("lng")
            if nb_lat is None or nb_lon is None:
                continue
            dist_nb = haversine(lat, lon, float(nb_lat), float(nb_lon))
            if dist_nb > radius:
                continue
            dist_str = f"📍 {dist_nb} км от вас\n"

            ebird_key = _ebird_obs_key(notable)
            neg_tid   = _ebird_taxon_hash((sci_name or com_name).lower())
            if not manual:
                if ebird_key in notified_obs_keys or neg_tid in recent_notified:
                    continue

            obs_dt    = notable.get("obsDt", "")[:10]
            how_many  = notable.get("howMany")
            count_str = f" · {how_many} особ." if how_many else ""
            loc_name  = notable.get("locName", "")

            text = (
                f"🚨 <b>{e(com_name)}</b>  <i>{e(sci_name)}</i>\n"
                f"\n🟡 Необычный вид для этого района{count_str}\n"
                f"{dist_str}"
                f"🕒 {obs_dt}\n"
                f"📌 {e(loc_name)}\n"
                f"\n<i>Необычное наблюдение рядом · eBird</i>"
            )
            loc_id = notable.get("locId", "")
            url    = f"https://ebird.org/checklist/{notable.get('subId', '')}" if notable.get("subId") else \
                     (f"https://ebird.org/hotspot/{loc_id}" if loc_id else "https://ebird.org")
            kb = InlineKeyboardMarkup(inline_keyboard=[[
                InlineKeyboardButton(text="Открыть на eBird →", url=url)
            ]])

            if manual:
                send_res = await safe_send_card(telegram_id, None, text, kb)
                if send_res == "blocked":
                    return
                found_any = True
                shown_names.add(com_name.lower())
                if sci_name:
                    shown_sci_names.add(sci_name.lower())
                sent_ebird += 1
            else:
                delivered, status = await _enqueue_and_deliver_notification(
                    telegram_id=telegram_id,
                    notif_type="rare_ebird",
                    dedup_key=ebird_key,
                    taxon_id=neg_tid,
                    obs_id=notable.get("obsId") or notable.get("subId"),
                    sci_name=sci_name or com_name,
                    photo_url=None,
                    text=text,
                    kb=kb,
                    now_str=now_str,
                )
                if status == "blocked":
                    return
                if delivered:
                    found_any = True
                    shown_names.add(com_name.lower())
                    if sci_name:
                        shown_sci_names.add(sci_name.lower())
                    notified_obs_keys.add(ebird_key)
                    recent_notified.add(neg_tid)
                    sent_ebird += 1

    if manual and not found_any:
        await bot.send_message(telegram_id, "✅ Пока нет редких птиц в вашем радиусе.")

# ================= ВИШЛИСТ ПРОВЕРКА =================
def _is_obs_older_than_notification(obs: dict, last_notified_at: str | None) -> bool:
    if not last_notified_at:
        return False
    try:
        notif_dt = datetime.fromisoformat(last_notified_at.replace("Z", "+00:00"))
        if notif_dt.tzinfo is None:
            notif_dt = notif_dt.replace(tzinfo=timezone.utc)
        obs_dt_str = obs.get("time_observed_at") or obs.get("created_at")
        if obs_dt_str:
            obs_dt = datetime.fromisoformat(obs_dt_str.replace("Z", "+00:00"))
            if obs_dt.tzinfo is None:
                obs_dt = obs_dt.replace(tzinfo=timezone.utc)
            return obs_dt <= notif_dt
        obs_on = obs.get("observed_on")
        if obs_on:
            obs_date = datetime.fromisoformat(obs_on[:10]).date()
            return obs_date < notif_dt.astimezone(timezone.utc).date()
    except Exception:
        pass
    return False

async def check_watchlist_for_user(telegram_id: int, observations: list | None = None):
    row = await db_fetch_one(
        "SELECT lat, lon, radius, period_days, alerts_enabled FROM users WHERE telegram_id = ?",
        (telegram_id,),
    )
    favs = await db_fetch_all(
        "SELECT taxon_id, taxon_name, last_notified_at, last_obs_id FROM favorites WHERE telegram_id = ?",
        (telegram_id,),
    )
    if not row or row[0] is None or not favs:
        return

    lat, lon, radius, days, alerts_enabled = row
    if not alerts_enabled:
        return
    taxon_ids = [f[0] for f in favs]

    if observations:
        latest_map: dict = {}
        watched_set = set(taxon_ids)
        for obs in observations:
            tid = obs["taxon"]["id"]
            if tid in watched_set and tid not in latest_map:
                obs_lat, obs_lon = _parse_obs_coords(obs)
                if obs_lat is not None and haversine(lat, lon, obs_lat, obs_lon) <= radius:
                    latest_map[tid] = obs
        missing = [tid for tid in taxon_ids if tid not in latest_map]
        if missing:
            extra = await get_batch_watchlist_observations(lat, lon, radius, days, missing)
            latest_map.update(extra)
    else:
        latest_map = await get_batch_watchlist_observations(lat, lon, radius, days, taxon_ids)

    now_str = datetime.now(timezone.utc).isoformat()

    for fav_row in favs:
        taxon_id         = fav_row[0]
        taxon_name       = fav_row[1]
        last_notified_at = fav_row[2]
        last_obs_id      = fav_row[3] if len(fav_row) > 3 else None

        obs = latest_map.get(taxon_id)
        if not obs:
            continue
        obs_id = obs.get("id")
        if last_obs_id is not None and obs_id is not None and int(obs_id) == int(last_obs_id):
            continue
        age = days_since(last_notified_at)
        if age is not None and age < 1:
            continue
        if _is_obs_older_than_notification(obs, last_notified_at):
            continue

        obs_lat, obs_lon = _parse_obs_coords(obs)
        if obs_lat is None:
            continue
        dist = haversine(lat, lon, obs_lat, obs_lon)
        if dist > radius:
            continue

        ago       = time_ago(obs.get("time_observed_at") or obs.get("observed_on"))
        photo_med = get_photo_url(obs, "medium")
        photo_ori = get_photo_url(obs, "original")
        url       = f"https://www.inaturalist.org/observations/{obs['id']}"

        taxon_cached_data = _get_taxon_cached(taxon_id)
        family_name, order_name = _extract_taxonomy(taxon_cached_data) if taxon_cached_data else ("", "")
        taxonomy_str = ""
        if order_name or family_name:
            taxonomy_str = "🔬 " + " · ".join(filter(None, [e(order_name), e(family_name)])) + "\n"

        sci = ""
        if obs.get("taxon", {}).get("name"):
            sci = obs["taxon"]["name"]

        text = (
            f"⭐ <b>{e(taxon_name)}</b>  <i>{e(sci)}</i>\n"
            f"{taxonomy_str}"
            f"\n⭐ Из вашего вишлиста\n"
            f"📍 {dist} км от вас\n"
            f"🕒 {ago}\n"
            f"\n<i>Птица из вишлиста замечена рядом · iNaturalist</i>"
        )
        kb_rows = [[InlineKeyboardButton(text="Открыть на iNaturalist →", url=url)]]
        if photo_ori:
            kb_rows.append([InlineKeyboardButton(text="🔍 Фото в полном размере", url=photo_ori)])
        kb = InlineKeyboardMarkup(inline_keyboard=kb_rows)

        dedup_key = f"wish:{taxon_id}:{obs_id if obs_id is not None else now_str[:10]}"
        _, status = await _enqueue_and_deliver_notification(
            telegram_id=telegram_id,
            notif_type="wishlist",
            dedup_key=dedup_key,
            taxon_id=taxon_id,
            obs_id=str(obs_id) if obs_id is not None else None,
            sci_name=sci,
            photo_url=photo_med,
            text=text,
            kb=kb,
            now_str=now_str,
        )
        if status == "blocked":
            return

# ================= 🔥 BIRD ALERT =================
async def check_bird_alert_for_user(telegram_id: int, lat: float, lon: float,
                                     radius: int, days: int,
                                     observations: list | None = None):
    if observations is None:
        observations = await get_recent_observations(lat, lon, radius, days)
    if not observations:
        return

    user_row = await db_fetch_one(
        "SELECT alerts_enabled, history_initialized FROM users WHERE telegram_id = ?",
        (telegram_id,),
    )
    if user_row and user_row[0] == 0:
        return
    history_initialized = bool(user_row[1]) if user_row else False

    now_str = datetime.now(timezone.utc).isoformat()
    history = {r[0]: r[1] for r in await db_fetch_all(
        "SELECT taxon_id, last_seen_at FROM species_history WHERE telegram_id = ?", (telegram_id,)
    )}

    seen: dict[int, dict] = {}
    for obs in observations:
        tid = obs["taxon"]["id"]
        if tid not in seen:
            obs_lat, obs_lon = _parse_obs_coords(obs)
            if obs_lat is not None and haversine(lat, lon, obs_lat, obs_lon) <= radius:
                seen[tid] = obs

    if not seen:
        return

    # Первичная инициализация истории пользователя фактическими датами наблюдений
    if not history and not history_initialized:
        try:
            async with db_transaction() as tx:
                await tx.executemany(
                    """INSERT INTO species_history (telegram_id, taxon_id, last_seen_at)
                       VALUES (?, ?, ?)
                       ON CONFLICT(telegram_id, taxon_id)
                       DO UPDATE SET last_seen_at = CASE
                           WHEN excluded.last_seen_at > species_history.last_seen_at
                           THEN excluded.last_seen_at
                           ELSE species_history.last_seen_at
                       END""",
                    [
                        (telegram_id, tid, _extract_obs_timestamp(obs, now_str))
                        for tid, obs in seen.items()
                    ],
                )
                await tx.execute(
                    """INSERT INTO users
                       (telegram_id, lat, lon, radius, period_days, alerts_enabled, season_filter, history_initialized)
                       VALUES (?, ?, ?, ?, ?, 1, 0, 1)
                       ON CONFLICT(telegram_id) DO UPDATE SET history_initialized = 1""",
                    (telegram_id, lat, lon, radius, days),
                )
        except Exception:
            logger.error(f"Ошибка инициализации species_history для user {telegram_id}", exc_info=True)
        return

    regular_seen_entries: list[tuple[int, int, str]] = []
    alerts_sent = 0
    user_blocked = False

    for tid, obs in seen.items():
        obs_seen_at = _extract_obs_timestamp(obs, now_str)
        absent_days = days_since(history.get(tid))
        if absent_days is None or absent_days >= BIRD_ALERT_DAYS:
            if not user_blocked and alerts_sent < 3:
                months_absent = (absent_days // 30) if absent_days else None
                taxon_obj = obs["taxon"]
                name      = taxon_obj.get("preferred_common_name") or taxon_obj["name"]
                sci       = taxon_obj.get("name", "")
                ago       = time_ago(obs.get("time_observed_at") or obs.get("observed_on"))
                photo_med = get_photo_url(obs, "medium")
                photo_ori = get_photo_url(obs, "original")
                url       = f"https://www.inaturalist.org/observations/{obs['id']}"
                obs_lat, obs_lon = _parse_obs_coords(obs)
                dist_str  = (f"📍 {haversine(lat, lon, obs_lat, obs_lon)} км от вас\n"
                             if obs_lat is not None else "")

                taxon_cached_data = _get_taxon_cached(tid)
                family_name, order_name = _extract_taxonomy(taxon_cached_data) if taxon_cached_data else ("", "")
                taxonomy_str = ""
                if order_name or family_name:
                    taxonomy_str = "🔬 " + " · ".join(filter(None, [e(order_name), e(family_name)])) + "\n"

                absent_note = (f"не наблюдался {months_absent} мес." if months_absent
                               else "ранее не наблюдался")
                text = (
                    f"🔥 <b>{e(name)}</b>  <i>{e(sci)}</i>\n"
                    f"{taxonomy_str}"
                    f"\n🔥 Впервые в вашем районе ({absent_note})\n"
                    f"{dist_str}"
                    f"🕒 {ago}\n"
                    f"\n<i>Bird Alert · iNaturalist</i>"
                )
                kb_rows = [[InlineKeyboardButton(text="Открыть на iNaturalist →", url=url)]]
                if photo_ori:
                    kb_rows.append([InlineKeyboardButton(text="🔍 Фото в полном размере", url=photo_ori)])
                kb = InlineKeyboardMarkup(inline_keyboard=kb_rows)

                dedup_key = f"alert:{tid}:{obs.get('id', now_str[:10])}"
                delivered, status = await _enqueue_and_deliver_notification(
                    telegram_id=telegram_id,
                    notif_type="bird_alert",
                    dedup_key=dedup_key,
                    taxon_id=tid,
                    obs_id=str(obs.get("id", "")),
                    sci_name=sci,
                    photo_url=photo_med,
                    text=text,
                    kb=kb,
                    now_str=now_str,
                    obs_seen_at=obs_seen_at,
                )
                if status == "blocked":
                    user_blocked = True
                elif delivered:
                    alerts_sent += 1
        else:
            regular_seen_entries.append((telegram_id, tid, obs_seen_at))

    # Обновляем last_seen_at фактической датой наблюдения (не затирая более свежую дату более старой)
    if regular_seen_entries:
        try:
            async with db_transaction() as tx:
                await tx.executemany(
                    """INSERT INTO species_history (telegram_id, taxon_id, last_seen_at)
                       VALUES (?, ?, ?)
                       ON CONFLICT(telegram_id, taxon_id)
                       DO UPDATE SET last_seen_at = CASE
                           WHEN excluded.last_seen_at > species_history.last_seen_at
                           THEN excluded.last_seen_at
                           ELSE species_history.last_seen_at
                       END""",
                    regular_seen_entries,
                )
        except Exception:
            logger.error(f"Ошибка обновления species_history для user {telegram_id}", exc_info=True)

# ================= ПЛАНИРОВЩИК =================
async def _run_checks_for_user(uid: int, lat: float, lon: float, radius: int, days: int):
    try:
        try:
            observations = await get_recent_observations(lat, lon, radius, days)
        except Exception:
            logger.error(f"Ошибка получения наблюдений для user {uid}", exc_info=True)
            observations = []

        check_names = (
            "check_rare_for_user",
            "check_bird_alert_for_user",
            "check_watchlist_for_user",
        )
        results = await asyncio.gather(
            check_rare_for_user(uid, manual=False, observations=observations),
            check_bird_alert_for_user(uid, lat, lon, radius, days, observations=observations),
            check_watchlist_for_user(uid, observations=observations),
            return_exceptions=True,
        )
        for check_name, res in zip(check_names, results):
            if isinstance(res, BaseException):
                logger.error(
                    f"Ошибка в фоновой проверке {check_name} для user {uid}: {res}",
                    exc_info=(type(res), res, res.__traceback__),
                )
    except Exception:
        logger.error(f"Ошибка при проверке пользователя {uid}", exc_info=True)

async def scheduled_checks():
    try:
        await process_pending_notifications()
    except Exception:
        logger.error("scheduled_checks: ошибка при обработке очереди pending-уведомлений", exc_info=True)

    users = await db_fetch_all(
        "SELECT telegram_id, lat, lon, radius, period_days "
        "FROM users WHERE alerts_enabled = 1 AND lat IS NOT NULL"
    )
    logger.info(f"scheduled_checks: запуск для {len(users)} пользователей")

    for i in range(0, len(users), SCHEDULER_BATCH_SIZE):
        batch = users[i:i + SCHEDULER_BATCH_SIZE]
        tasks = [_run_checks_for_user(*u) for u in batch]
        try:
            batch_results = await asyncio.wait_for(
                asyncio.gather(*tasks, return_exceptions=True),
                timeout=90,
            )
            for u, res in zip(batch, batch_results):
                if isinstance(res, BaseException):
                    logger.error(
                        f"scheduled_checks: исключение для пользователя {u[0]}: {res}",
                        exc_info=(type(res), res, res.__traceback__),
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

    uid = inline_query.from_user.id

    user_row = await db_fetch_one(
        "SELECT lat, lon, radius, period_days FROM users WHERE telegram_id = ?", (uid,)
    )

    taxa    = await search_taxa_by_name(query)
    results = []

    nearest_obs: dict[int, dict] = {}
    if user_row and user_row[0] is not None and taxa:
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

        description  = sci_name
        nearest_text = ""
        if tid in nearest_obs and user_row:
            obs = nearest_obs[tid]
            ago = time_ago(obs.get("time_observed_at") or obs.get("observed_on"))
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
    global http_session, db_conn, BOT_USERNAME, _api_semaphore, _ebird_semaphore, _tg_send_semaphore

    try:
        await init_db()
    except Exception:
        logger.critical("Не удалось инициализировать БД", exc_info=True)
        raise

    db_conn = await aiosqlite.connect(DB_NAME, check_same_thread=False, isolation_level=None)
    await db_conn.execute("PRAGMA journal_mode=WAL")
    await db_conn.execute("PRAGMA synchronous=NORMAL")
    await db_conn.execute("PRAGMA busy_timeout=5000")
    db_conn.row_factory = aiosqlite.Row

    http_session = aiohttp.ClientSession(
        connector=aiohttp.TCPConnector(limit=20, limit_per_host=API_SEMAPHORE_LIMIT)
    )
    _api_semaphore     = asyncio.Semaphore(API_SEMAPHORE_LIMIT)
    _ebird_semaphore   = asyncio.Semaphore(EBIRD_SEMAPHORE_LIMIT)
    _tg_send_semaphore = asyncio.Semaphore(TG_SEND_SEMAPHORE_LIMIT)

    bot_info     = await bot.get_me()
    BOT_USERNAME = bot_info.username
    logger.info(f"Бот запущен как @{BOT_USERNAME}")

    if EBIRD_API_KEY:
        logger.info("eBird API ключ найден — хотспоты и notable birds активны")
    else:
        logger.info("EBIRD_API_KEY не задан — eBird-функции отключены")

    # Восстановление незавершённых уведомлений после перезапуска
    try:
        await process_pending_notifications()
    except Exception:
        logger.error("Ошибка восстановления очереди уведомлений при старте", exc_info=True)

    scheduler = AsyncIOScheduler()
    scheduler.add_job(scheduled_checks,            "interval", hours=1,
                      max_instances=1, misfire_grace_time=300)
    scheduler.add_job(_cleanup_scan_cache,         "interval", minutes=10)
    scheduler.add_job(_cleanup_cooldowns,          "interval", minutes=5)
    scheduler.add_job(_cleanup_rare_notifications, "interval", hours=6)
    scheduler.start()

    logger.info("🚀 BAM бот запущен!")
    try:
        await dp.start_polling(bot)
    finally:
        scheduler.shutdown(wait=False)
        await http_session.close()
        await db_conn.close()
        await bot.session.close()
        logger.info("✅ Бот остановлен, ресурсы освобождены.")

if __name__ == "__main__":
    asyncio.run(main())
