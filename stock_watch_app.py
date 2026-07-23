import argparse
import ctypes
import html
import json
import math
import os
import queue
import re
import threading
import time
import tkinter as tk
import urllib.parse
import urllib.request
from collections import deque
from dataclasses import asdict, dataclass, field
from datetime import datetime, timedelta
from pathlib import Path
from tkinter import messagebox, ttk

import winsound
from futu import AuType, KLType, OpenQuoteContext, RET_ERROR, RET_OK, StockQuoteHandlerBase, SubType


APP_DIR = Path(__file__).resolve().parent
CONFIG_PATH = APP_DIR / "stock_watch_config.json"
LOG_PATH = APP_DIR / "stock_watch_app.log"
ALERT_COOLDOWN_SECONDS = 60 * 60
SNAPSHOT_BATCH_SIZE = 400
SNAPSHOT_RATE_LIMIT = 55
SNAPSHOT_RATE_WINDOW_SECONDS = 30.0
SNAPSHOT_CACHE_TTL_SECONDS = 20.0
QUOTE_SUBSCRIBE_BATCH_SIZE = 400
KLINE_CACHE_TTL_SECONDS = 5 * 60.0
KLINE_REFRESH_PER_TICK = 3
DIVIDEND_RATE_LIMIT = 20
DIVIDEND_RATE_WINDOW_SECONDS = 30.0
CAPITAL_FLOW_RATE_LIMIT = 25
CAPITAL_FLOW_RATE_WINDOW_SECONDS = 30.0
CAPITAL_FLOW_CACHE_TTL_SECONDS = 60.0
ETF_SHARE_RATE_LIMIT = 10
ETF_SHARE_RATE_WINDOW_SECONDS = 30.0
ETF_SHARE_CACHE_TTL_SECONDS = 6 * 60 * 60.0
QUOTE_COLUMNS = (
    "code",
    "name",
    "price",
    "change_pct",
    "turnover",
    "turnover_rate",
    "volume_ratio",
    "intraday_pos",
    "premium_rate",
    "vwap_dev",
    "capital_flow",
    "bid_ask_ratio",
    "dividend_yield",
    "rsi",
    "kdj",
    "boll",
    "ma",
    "ma_dev",
    "yhigh_drawdown",
    "atr_pct",
    "breakout",
    "update",
    "status",
)
DEFAULT_DISPLAY_COLUMNS = [
    "code",
    "name",
    "price",
    "change_pct",
    "turnover",
    "turnover_rate",
    "volume_ratio",
    "intraday_pos",
    "premium_rate",
    "vwap_dev",
    "capital_flow",
    "bid_ask_ratio",
    "dividend_yield",
    "rsi",
    "boll",
    "ma_dev",
    "yhigh_drawdown",
    "atr_pct",
    "breakout",
    "status",
]


def write_log(message: str) -> None:
    line = f"{datetime.now():%Y-%m-%d %H:%M:%S} {message}"
    with LOG_PATH.open("a", encoding="utf-8") as f:
        f.write(line + "\n")


def normalize_code(raw: str) -> str:
    code = raw.strip().upper()
    if "." in code:
        return code
    if len(code) == 6 and code.isdigit():
        if code.startswith(("5", "6", "7", "9")):
            return f"SH.{code}"
        if code.startswith(("0", "1", "2", "3")):
            return f"SZ.{code}"
    return code


def lookup_stock_name(code: str) -> str:
    normalized = normalize_code(code)
    if not normalized:
        return ""
    ctx = OpenQuoteContext(host="127.0.0.1", port=11111)
    try:
        ret, data = ctx.get_market_snapshot([normalized])
        if ret != RET_OK:
            raise RuntimeError(str(data))
        return str(data.iloc[0].get("name", "")).strip()
    finally:
        ctx.close()


def cn_sma(values: list[float], period: int, weight: int = 1) -> float:
    if not values:
        return math.nan
    result = values[0]
    for value in values[1:]:
        result = (weight * value + (period - weight) * result) / period
    return result


def rsi_cn(closes: list[float], period: int) -> float:
    if len(closes) < period + 1:
        return math.nan
    diffs = [closes[i] - closes[i - 1] for i in range(1, len(closes))]
    gains = [max(change, 0.0) for change in diffs]
    abs_changes = [abs(change) for change in diffs]
    avg_gain = cn_sma(gains, period, 1)
    avg_change = cn_sma(abs_changes, period, 1)
    if avg_gain == 0 and avg_change == 0:
        return 50.0
    if avg_change == 0:
        return 100.0
    return avg_gain / avg_change * 100.0


def boll(closes: list[float], period: int, mult: float) -> tuple[float, float, float]:
    if len(closes) < period:
        return math.nan, math.nan, math.nan
    window = closes[-period:]
    mid = sum(window) / period
    variance = sum((x - mid) ** 2 for x in window) / period
    std = math.sqrt(variance)
    return mid, mid + mult * std, mid - mult * std


def moving_average(closes: list[float], period: int) -> float:
    if len(closes) < period:
        return math.nan
    return sum(closes[-period:]) / period


def atr_percent(highs: list[float], lows: list[float], closes: list[float], period: int = 14) -> float:
    if len(closes) < period + 1 or len(highs) != len(closes) or len(lows) != len(closes):
        return math.nan
    true_ranges = []
    start = len(closes) - period
    for index in range(start, len(closes)):
        prev_close = closes[index - 1]
        true_ranges.append(
            max(
                highs[index] - lows[index],
                abs(highs[index] - prev_close),
                abs(lows[index] - prev_close),
            )
        )
    price = closes[-1]
    if price == 0:
        return math.nan
    return sum(true_ranges) / period / price * 100


def breakout_text(highs: list[float], lows: list[float], price: float, period: int = 20) -> str:
    if len(highs) <= period or len(lows) <= period:
        return ""
    prev_high = max(highs[-period - 1 : -1])
    prev_low = min(lows[-period - 1 : -1])
    if price >= prev_high:
        return f"{period}日新高"
    if price <= prev_low:
        return f"{period}日新低"
    return ""


def migrate_display_columns(columns: list[str]) -> list[str]:
    known = set(QUOTE_COLUMNS)
    migrated = []
    for col in columns:
        if col not in known or col in migrated:
            continue
        migrated.append(col)
    if not migrated:
        return list(DEFAULT_DISPLAY_COLUMNS)
    for col in DEFAULT_DISPLAY_COLUMNS:
        if col in known and col not in migrated:
            migrated.append(col)
    return migrated


def parse_dividend_date(text: str) -> datetime | None:
    if not text:
        return None
    for fmt in ("%Y-%m-%d", "%Y/%m/%d", "%Y.%m.%d", "%Y%m%d"):
        try:
            return datetime.strptime(str(text).strip(), fmt)
        except ValueError:
            continue
    return None


def parse_cash_dividend_per_unit(statement: str) -> float | None:
    text = str(statement or "").replace(",", "").strip()
    if not text:
        return None

    cash_patterns = [
        r"(?:每\s*)?10\s*(?:股|份|份基金份额|股股份|单位)?[^0-9]*(?:派|派发|派现|分配|现金红利|红利)[^0-9]*([0-9]+(?:\.[0-9]+)?)\s*元",
        r"(?:每\s*)?1\s*(?:股|份|份基金份额|股股份|单位)?[^0-9]*(?:派|派发|派现|分配|现金红利|红利)[^0-9]*([0-9]+(?:\.[0-9]+)?)\s*元",
        r"(?:派|派发|派现|分配|现金红利|红利)[^0-9]*([0-9]+(?:\.[0-9]+)?)\s*元\s*/\s*(?:股|份|单位)",
        r"(?:每股|每份|每单位)[^0-9]*(?:派|派发|派现|分配|现金红利|红利)?[^0-9]*([0-9]+(?:\.[0-9]+)?)\s*元",
        r"10\s*派\s*([0-9]+(?:\.[0-9]+)?)",
    ]
    for pattern in cash_patterns:
        match = re.search(pattern, text)
        if not match:
            continue
        amount = float(match.group(1))
        return amount / 10 if "10" in pattern[:20] else amount
    return None


def strip_html_tags(text: str) -> str:
    return html.unescape(re.sub(r"<[^>]+>", "", text)).strip()


def fetch_eastmoney_fund_dividends(code: str) -> list[dict]:
    fund_code = code.split(".", 1)[-1]
    if not (len(fund_code) == 6 and fund_code.isdigit()):
        return []
    url = f"https://fundf10.eastmoney.com/fhsp_{fund_code}.html"
    request = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(request, timeout=8) as response:
        text = response.read().decode("utf-8", errors="ignore")
    rows = []
    for match in re.finditer(r"<tr>(.*?)</tr>", text, flags=re.IGNORECASE | re.DOTALL):
        cells = re.findall(r"<td[^>]*>(.*?)</td>", match.group(1), flags=re.IGNORECASE | re.DOTALL)
        if len(cells) < 5:
            continue
        rows.append(
            {
                "pub_date": strip_html_tags(cells[0]),
                "record_date": strip_html_tags(cells[1]),
                "ex_date": strip_html_tags(cells[2]),
                "statement": strip_html_tags(cells[3]),
                "dividend_payable_date": strip_html_tags(cells[4]),
            }
        )
    return rows


def parse_jsonp_payload(text: str) -> dict:
    start = text.find("(")
    end = text.rfind(")")
    if start == -1 or end == -1 or end <= start:
        return json.loads(text)
    return json.loads(text[start + 1 : end])


def fetch_sse_etf_total_units(code: str) -> float | None:
    normalized = normalize_code(code)
    if not normalized.startswith("SH."):
        return None
    fund_code = normalized.split(".", 1)[-1]
    if not (len(fund_code) == 6 and fund_code.isdigit()):
        return None
    params = {
        "jsonCallBack": "jsonpCallback",
        "isPagination": "true",
        "pageHelp.pageSize": "1000",
        "pageHelp.pageNo": "1",
        "pageHelp.beginPage": "1",
        "pageHelp.cacheSize": "1",
        "pageHelp.endPage": "1",
        "sqlId": "COMMON_SSE_ZQPZ_ETFZL_XXPL_ETFGM_SEARCH_L",
        "STAT_DATE": "",
    }
    url = "https://query.sse.com.cn/commonQuery.do?" + urllib.parse.urlencode(params)
    request = urllib.request.Request(
        url,
        headers={
            "Referer": "https://www.sse.com.cn/market/funddata/volumn/etfvolumn/",
            "User-Agent": "Mozilla/5.0",
        },
    )
    with urllib.request.urlopen(request, timeout=10) as response:
        text = response.read().decode("utf-8", errors="ignore")
    payload = parse_jsonp_payload(text)
    rows = payload.get("pageHelp", {}).get("data", [])
    for row in rows:
        if str(row.get("SEC_CODE", "")).strip() != fund_code:
            continue
        total_10k_units = safe_parse_number(row.get("TOT_VOL"))
        if total_10k_units and total_10k_units > 0:
            return total_10k_units * 10000
    return None


def futu_code_to_tushare(code: str) -> str | None:
    normalized = normalize_code(code)
    if "." not in normalized:
        return None
    market, fund_code = normalized.split(".", 1)
    if market not in {"SH", "SZ"} or not (len(fund_code) == 6 and fund_code.isdigit()):
        return None
    suffix = "SH" if market == "SH" else "SZ"
    return f"{fund_code}.{suffix}"


def fetch_tushare_etf_total_units(code: str) -> float | None:
    token = os.environ.get("TUSHARE_TOKEN", "").strip()
    if not token:
        return None
    ts_code = futu_code_to_tushare(code)
    if not ts_code:
        return None
    body = json.dumps(
        {
            "api_name": "etf_share_size",
            "token": token,
            "params": {"ts_code": ts_code},
            "fields": "trade_date,ts_code,total_share,exchange",
        }
    ).encode("utf-8")
    request = urllib.request.Request(
        "https://api.tushare.pro",
        data=body,
        headers={"Content-Type": "application/json", "User-Agent": "Mozilla/5.0"},
        method="POST",
    )
    with urllib.request.urlopen(request, timeout=10) as response:
        payload = json.loads(response.read().decode("utf-8", errors="ignore"))
    if payload.get("code") not in (0, "0", None):
        raise RuntimeError(payload.get("msg") or payload)
    data = payload.get("data") or {}
    fields = list(data.get("fields") or [])
    items = list(data.get("items") or [])
    if not fields or not items or "total_share" not in fields:
        return None
    if "trade_date" in fields:
        date_index = fields.index("trade_date")
        items.sort(key=lambda item: str(item[date_index] if len(item) > date_index else ""), reverse=True)
    index = fields.index("total_share")
    total_10k_units = safe_parse_number(items[0][index] if len(items[0]) > index else None)
    if total_10k_units and total_10k_units > 0:
        return total_10k_units * 10000
    return None


def safe_parse_number(value) -> float | None:
    try:
        text = str(value).replace(",", "").strip()
        if not text or text == "-":
            return None
        numeric = float(text)
        if math.isnan(numeric):
            return None
        return numeric
    except Exception:
        return None


def fetch_external_etf_total_units(code: str) -> float | None:
    return fetch_sse_etf_total_units(code) or fetch_tushare_etf_total_units(code)


def parse_periods(text: str) -> list[int]:
    periods = []
    for token in text.replace("，", ",").replace("/", ",").replace(" ", ",").split(","):
        token = token.strip()
        if not token:
            continue
        value = int(token)
        if value <= 0:
            raise ValueError("均线周期必须大于 0")
        periods.append(value)
    return sorted(set(periods))


def kdj(
    highs: list[float],
    lows: list[float],
    closes: list[float],
    period: int,
    smooth_k: int = 3,
    smooth_d: int = 3,
) -> tuple[float, float, float]:
    if len(closes) < period:
        return math.nan, math.nan, math.nan
    rsv_values: list[float] = []
    for i in range(period - 1, len(closes)):
        high_n = max(highs[i - period + 1 : i + 1])
        low_n = min(lows[i - period + 1 : i + 1])
        if high_n == low_n:
            rsv = 50.0
        else:
            rsv = (closes[i] - low_n) / (high_n - low_n) * 100.0
        rsv_values.append(rsv)
    k_values: list[float] = []
    k_value = 50.0
    for rsv in rsv_values:
        k_value = (rsv + (smooth_k - 1) * k_value) / smooth_k
        k_values.append(k_value)
    d_value = 50.0
    for k_item in k_values:
        d_value = (k_item + (smooth_d - 1) * d_value) / smooth_d
    k_last = k_values[-1]
    return k_last, d_value, 3 * k_last - 2 * d_value


@dataclass
class IndicatorSettings:
    rsi_enabled: bool = True
    rsi_period: int = 6
    rsi_low: float = 20.0
    rsi_high: float = 80.0
    kdj_enabled: bool = False
    kdj_period: int = 9
    kdj_low: float = 20.0
    kdj_high: float = 80.0
    kdj_line: str = "J"
    boll_enabled: bool = True
    boll_period: int = 20
    boll_mult: float = 2.0
    boll_touch_lower: bool = True
    boll_touch_upper: bool = True
    ma_enabled: bool = False
    ma_periods: str = "5,10,20,60,120,220,250"
    ma_cross_up_action: str = "买入"
    ma_cross_down_action: str = "卖出"


@dataclass
class WatchItem:
    code: str
    name: str = ""
    enabled: bool = True
    refresh_seconds: int = 30
    settings: IndicatorSettings = field(default_factory=IndicatorSettings)


@dataclass
class AppConfig:
    interval_seconds: int = 30
    popup_enabled: bool = True
    sound_enabled: bool = True
    display_columns: list[str] = field(default_factory=lambda: list(DEFAULT_DISPLAY_COLUMNS))
    quote_column_widths: dict[str, int] = field(default_factory=dict)
    items: list[WatchItem] = field(default_factory=list)


def config_from_dict(data: dict) -> AppConfig:
    items = []
    for item_data in data.get("items", []):
        settings = IndicatorSettings(**item_data.get("settings", {}))
        items.append(
            WatchItem(
                code=item_data.get("code", ""),
                name=item_data.get("name", ""),
                enabled=item_data.get("enabled", True),
                refresh_seconds=max(1, int(item_data.get("refresh_seconds", data.get("interval_seconds", 30)))),
                settings=settings,
            )
        )
    return AppConfig(
        interval_seconds=int(data.get("interval_seconds", 30)),
        popup_enabled=bool(data.get("popup_enabled", True)),
        sound_enabled=bool(data.get("sound_enabled", True)),
        display_columns=migrate_display_columns(list(data.get("display_columns", DEFAULT_DISPLAY_COLUMNS))),
        quote_column_widths=dict(data.get("quote_column_widths", {})),
        items=items,
    )


def load_config() -> AppConfig:
    if CONFIG_PATH.exists():
        return config_from_dict(json.loads(CONFIG_PATH.read_text(encoding="utf-8")))
    return AppConfig(
        items=[
            WatchItem(
                code="SH.515450",
                name="红利低波50ETF南方",
                refresh_seconds=30,
                settings=IndicatorSettings(),
            )
        ]
    )


def save_config(config: AppConfig) -> None:
    CONFIG_PATH.write_text(
        json.dumps(asdict(config), ensure_ascii=False, indent=2),
        encoding="utf-8",
    )


class AlertManager:
    def __init__(self, popup_enabled: bool, sound_enabled: bool):
        self.popup_enabled = popup_enabled
        self.sound_enabled = sound_enabled

    def configure(self, popup_enabled: bool, sound_enabled: bool) -> None:
        self.popup_enabled = popup_enabled
        self.sound_enabled = sound_enabled

    def trigger(self, message: str) -> None:
        write_log("ALERT " + message)
        if self.popup_enabled:
            threading.Thread(target=self._popup_alert, args=(message,), daemon=True).start()
        elif self.sound_enabled:
            threading.Thread(target=self._short_sound, daemon=True).start()

    def _short_sound(self) -> None:
        try:
            winsound.Beep(1200, 450)
            winsound.Beep(900, 450)
        except Exception:
            pass

    def _popup_alert(self, message: str) -> None:
        stop_sound = threading.Event()
        sound_thread = None
        if self.sound_enabled:
            sound_thread = threading.Thread(target=self._sound_loop, args=(stop_sound,), daemon=True)
            sound_thread.start()
        try:
            ctypes.windll.user32.MessageBoxW(0, message, "盯盘提醒", 0x40)
        except Exception:
            pass
        finally:
            stop_sound.set()
            if sound_thread:
                sound_thread.join(timeout=2)

    def _sound_loop(self, stop_sound: threading.Event) -> None:
        while not stop_sound.is_set():
            try:
                winsound.Beep(1200, 450)
                winsound.Beep(900, 450)
            except Exception:
                time.sleep(1)
            stop_sound.wait(1)


class RollingRateLimiter:
    def __init__(self, max_calls: int, window_seconds: float):
        self.max_calls = max_calls
        self.window_seconds = window_seconds
        self.calls: deque[float] = deque()
        self.lock = threading.Lock()

    def wait(self, stop_event: threading.Event) -> bool:
        while not stop_event.is_set():
            with self.lock:
                now = time.time()
                while self.calls and now - self.calls[0] >= self.window_seconds:
                    self.calls.popleft()
                if len(self.calls) < self.max_calls:
                    self.calls.append(now)
                    return True
                sleep_for = max(0.05, self.window_seconds - (now - self.calls[0]) + 0.05)
            if stop_event.wait(min(sleep_for, 1.0)):
                return False
        return False

    def available(self) -> int:
        with self.lock:
            now = time.time()
            while self.calls and now - self.calls[0] >= self.window_seconds:
                self.calls.popleft()
            return max(0, self.max_calls - len(self.calls))


class MarketDataCache:
    def __init__(self) -> None:
        self.lock = threading.Lock()
        self.snapshots: dict[str, tuple[float, dict]] = {}
        self.quotes: dict[str, tuple[float, dict]] = {}
        self.klines: dict[str, tuple[float, list[float], list[float], list[float]]] = {}

    def update_snapshot_rows(self, data) -> None:
        now = time.time()
        rows = self._records(data)
        with self.lock:
            for row in rows:
                code = str(row.get("code", "")).strip()
                if code:
                    self.snapshots[code] = (now, row)

    def update_quote_rows(self, data) -> None:
        now = time.time()
        rows = self._records(data)
        with self.lock:
            for row in rows:
                code = str(row.get("code", "")).strip()
                if code:
                    self.quotes[code] = (now, row)

    def update_kline(self, code: str, closes: list[float], highs: list[float], lows: list[float]) -> None:
        with self.lock:
            self.klines[code] = (time.time(), closes, highs, lows)

    def get_market_row(self, code: str) -> tuple[dict | None, float | None]:
        with self.lock:
            snapshot_item = self.snapshots.get(code)
            quote_item = self.quotes.get(code)
            if not snapshot_item and not quote_item:
                return None, None
            row = dict(snapshot_item[1]) if snapshot_item else {}
            row_time = snapshot_item[0] if snapshot_item else None
            if quote_item:
                row.update(quote_item[1])
                row_time = max(row_time or 0, quote_item[0])
            return row, row_time

    def get_kline(self, code: str) -> tuple[float, list[float], list[float], list[float]] | None:
        with self.lock:
            item = self.klines.get(code)
            if not item:
                return None
            ts, closes, highs, lows = item
            return ts, list(closes), list(highs), list(lows)

    def snapshot_age(self, code: str) -> float | None:
        with self.lock:
            item = self.snapshots.get(code)
            return None if not item else time.time() - item[0]

    def kline_age(self, code: str) -> float | None:
        with self.lock:
            item = self.klines.get(code)
            return None if not item else time.time() - item[0]

    def _records(self, data) -> list[dict]:
        if data is None:
            return []
        if hasattr(data, "to_dict"):
            try:
                return list(data.to_dict("records"))
            except Exception:
                pass
        if isinstance(data, list):
            return [dict(row) for row in data if hasattr(row, "items")]
        if hasattr(data, "items"):
            return [dict(data)]
        return []


class CachedQuoteHandler(StockQuoteHandlerBase):
    def __init__(self, cache: MarketDataCache):
        super().__init__()
        self.cache = cache

    def on_recv_rsp(self, rsp_pb):
        ret_code, data = super().on_recv_rsp(rsp_pb)
        if ret_code != RET_OK:
            write_log(f"ERROR quote push {data}")
            return RET_ERROR, data
        self.cache.update_quote_rows(data)
        return RET_OK, data


class MonitorThread(threading.Thread):
    def __init__(self, app_queue: queue.Queue, alert_manager: AlertManager):
        super().__init__(daemon=True)
        self.app_queue = app_queue
        self.alert_manager = alert_manager
        self.stop_event = threading.Event()
        self.config_lock = threading.Lock()
        self.config = load_config()
        self.triggered: set[str] = set()
        self.active_signal_keys: dict[str, str] = {}
        self.last_alert_at: dict[str, float] = {}
        self.subscribed: set[str] = set()
        self.kline_subscribed: set[str] = set()
        self.subscribe_retry_at: dict[str, float] = {}
        self.last_poll_at: dict[str, float] = {}
        self.dividend_cache: dict[str, tuple[float, float]] = {}
        self.dividend_pending: set[str] = set()
        self.dividend_queue: deque[str] = deque()
        self.dividend_lock = threading.Lock()
        self.dividend_limiter = RollingRateLimiter(DIVIDEND_RATE_LIMIT, DIVIDEND_RATE_WINDOW_SECONDS)
        self.dividend_worker: threading.Thread | None = None
        self.capital_flow_cache: dict[str, tuple[float, float]] = {}
        self.capital_flow_pending: set[str] = set()
        self.capital_flow_queue: deque[str] = deque()
        self.capital_flow_lock = threading.Lock()
        self.capital_flow_limiter = RollingRateLimiter(CAPITAL_FLOW_RATE_LIMIT, CAPITAL_FLOW_RATE_WINDOW_SECONDS)
        self.capital_flow_worker: threading.Thread | None = None
        self.etf_share_cache: dict[str, tuple[float, float]] = {}
        self.etf_share_pending: set[str] = set()
        self.etf_share_queue: deque[str] = deque()
        self.etf_share_lock = threading.Lock()
        self.etf_share_limiter = RollingRateLimiter(ETF_SHARE_RATE_LIMIT, ETF_SHARE_RATE_WINDOW_SECONDS)
        self.etf_share_worker: threading.Thread | None = None
        self.cache = MarketDataCache()
        self.snapshot_limiter = RollingRateLimiter(SNAPSHOT_RATE_LIMIT, SNAPSHOT_RATE_WINDOW_SECONDS)
        self.last_emit_at: dict[str, float] = {}

    def update_config(self, config: AppConfig) -> None:
        with self.config_lock:
            self.config = config
        self.alert_manager.configure(config.popup_enabled, config.sound_enabled)

    def stop(self) -> None:
        self.stop_event.set()

    def run(self) -> None:
        ctx = None
        try:
            ctx = OpenQuoteContext(host="127.0.0.1", port=11111)
            ctx.set_handler(CachedQuoteHandler(self.cache))
            self._ensure_dividend_worker()
            self._ensure_capital_flow_worker()
            self._ensure_etf_share_worker()
            self.app_queue.put(("status", "已连接 Futu OpenD"))
            while not self.stop_event.is_set():
                with self.config_lock:
                    config = config_from_dict(json.loads(json.dumps(asdict(self.config), ensure_ascii=False)))
                items = [item for item in config.items if item.enabled and item.code]
                codes = [normalize_code(item.code) for item in items]
                self._ensure_subscribed(ctx, codes)
                self._refresh_due_snapshots(ctx, items, config)
                self._refresh_due_klines(ctx, items)
                self._emit_due_items(items, config)
                self.stop_event.wait(1)
        except Exception as exc:
            write_log(f"ERROR monitor stopped: {exc}")
            self.app_queue.put(("status", f"监控异常：{exc}"))
        finally:
            if ctx:
                ctx.close()

    def _ensure_subscribed(self, ctx: OpenQuoteContext, codes: list[str]) -> None:
        now = time.time()
        missing = [
            code
            for code in dict.fromkeys(codes)
            if code not in self.subscribed and now >= self.subscribe_retry_at.get(code, 0)
        ]
        for batch in self._chunks(missing, QUOTE_SUBSCRIBE_BATCH_SIZE):
            ret, data = ctx.subscribe(batch, [SubType.QUOTE], is_first_push=True, subscribe_push=True)
            if ret != RET_OK:
                write_log(f"ERROR subscribe {batch[:3]}... {data}")
                retry_at = time.time() + 60
                for code in batch:
                    self.subscribe_retry_at[code] = retry_at
                continue
            self.subscribed.update(batch)

    def _refresh_due_snapshots(self, ctx: OpenQuoteContext, items: list[WatchItem], config: AppConfig) -> None:
        now = time.time()
        due_codes: list[str] = []
        seen = set()
        for item in items:
            code = normalize_code(item.code)
            if code in seen:
                continue
            seen.add(code)
            interval = max(SNAPSHOT_CACHE_TTL_SECONDS, float(item.refresh_seconds or config.interval_seconds))
            last = self.last_poll_at.get(code, 0)
            if now - last >= interval or self.cache.snapshot_age(code) is None:
                due_codes.append(code)

        for batch in self._chunks(due_codes, SNAPSHOT_BATCH_SIZE):
            if not self.snapshot_limiter.wait(self.stop_event):
                return
            ret, snap = ctx.get_market_snapshot(batch)
            if ret != RET_OK:
                message = str(snap)
                write_log(f"ERROR batch snapshot size={len(batch)} {message}")
                self.app_queue.put(("status", f"批量快照失败：{message}；剩余额度 {self.snapshot_limiter.available()}/{SNAPSHOT_RATE_LIMIT}"))
                continue
            self.cache.update_snapshot_rows(snap)
            poll_time = time.time()
            for code in batch:
                self.last_poll_at[code] = poll_time
            self.app_queue.put(("status", f"批量快照 {len(batch)} 只；剩余额度 {self.snapshot_limiter.available()}/{SNAPSHOT_RATE_LIMIT}"))

    def _refresh_due_klines(self, ctx: OpenQuoteContext, items: list[WatchItem]) -> None:
        refreshed = 0
        seen = set()
        for item in items:
            if refreshed >= KLINE_REFRESH_PER_TICK or self.stop_event.is_set():
                return
            code = normalize_code(item.code)
            if code in seen:
                continue
            seen.add(code)
            age = self.cache.kline_age(code)
            if age is not None and age < KLINE_CACHE_TTL_SECONDS:
                continue
            try:
                if code not in self.kline_subscribed:
                    ret, data = ctx.subscribe([code], [SubType.K_DAY], subscribe_push=False)
                    if ret != RET_OK:
                        raise RuntimeError(str(data))
                    self.kline_subscribed.add(code)
                ret, kline = ctx.get_cur_kline(code, 300, KLType.K_DAY, autype=AuType.QFQ)
                if ret != RET_OK:
                    raise RuntimeError(str(kline))
                closes = [float(x) for x in kline["close"].tolist()]
                highs = [float(x) for x in kline["high"].tolist()]
                lows = [float(x) for x in kline["low"].tolist()]
                self.cache.update_kline(code, closes, highs, lows)
                refreshed += 1
            except Exception as exc:
                write_log(f"ERROR kline {code} {exc}")

    def _emit_due_items(self, items: list[WatchItem], config: AppConfig) -> None:
        now = time.time()
        for item in items:
            if self.stop_event.is_set():
                return
            code = normalize_code(item.code)
            interval = max(1, int(item.refresh_seconds or config.interval_seconds))
            if now - self.last_emit_at.get(code, 0) < interval:
                continue
            self._poll_item(item)
            self.last_emit_at[code] = now

    def _poll_item(self, item: WatchItem) -> None:
        try:
            code = normalize_code(item.code)
            row, _row_time = self.cache.get_market_row(code)
            if not row:
                return
            price = float(row["last_price"])
            price_decimals = self._price_decimals(row)
            name = str(row.get("name", item.name or code))
            update_time = str(row.get("update_time", ""))
            kline_item = self.cache.get_kline(code)
            if kline_item:
                _kline_time, raw_closes, highs, lows = kline_item
                closes = list(raw_closes)
                if closes:
                    closes[-1] = price
                    highs[-1] = max(highs[-1], price)
                    lows[-1] = min(lows[-1], price)
            else:
                raw_closes, closes, highs, lows = [], [], [], []

            settings = item.settings
            values: dict[str, float] = {"price": price, "price_decimals": price_decimals}
            prev_close_price = self._safe_float(row.get("prev_close_price"))
            if prev_close_price is not None and prev_close_price > 0:
                values["change_val"] = price - prev_close_price
                values["change_pct"] = (price - prev_close_price) / prev_close_price * 100
            turnover = self._safe_float(row.get("turnover"))
            if turnover is not None:
                values["turnover"] = turnover
            turnover_rate = self._safe_float(row.get("turnover_rate"))
            if turnover_rate is not None and turnover_rate > 0:
                values["turnover_rate"] = turnover_rate
            else:
                calculated_turnover_rate = self._calculated_turnover_rate(code, row)
                if calculated_turnover_rate is not None:
                    values["turnover_rate"] = calculated_turnover_rate
                    values["turnover_rate_calc"] = 1.0
            volume_ratio = self._safe_float(row.get("volume_ratio"))
            if volume_ratio is not None:
                values["volume_ratio"] = volume_ratio
            high_price = self._safe_float(row.get("high_price"))
            low_price = self._safe_float(row.get("low_price"))
            if high_price is not None and low_price is not None and high_price > low_price:
                values["intraday_pos"] = (price - low_price) / (high_price - low_price) * 100
            premium_rate = self._snapshot_premium_rate(row, price)
            if premium_rate is not None:
                values["premium_rate"] = premium_rate
            avg_price = self._safe_float(row.get("avg_price"))
            if avg_price is not None and avg_price > 0:
                values["vwap_dev"] = (price - avg_price) / avg_price * 100
            bid_ask_ratio = self._safe_float(row.get("bid_ask_ratio"))
            if bid_ask_ratio is not None:
                values["bid_ask_ratio"] = bid_ask_ratio
            capital_flow = self._capital_net_inflow(code)
            if capital_flow is not None:
                values["capital_flow"] = capital_flow
            if settings.rsi_enabled:
                values["rsi"] = rsi_cn(closes, settings.rsi_period)
            if settings.kdj_enabled:
                k_value, d_value, j_value = kdj(highs, lows, closes, settings.kdj_period)
                values["kdj_k"] = k_value
                values["kdj_d"] = d_value
                values["kdj_j"] = j_value
            if settings.boll_enabled:
                mid, upper, lower = boll(closes, settings.boll_period, settings.boll_mult)
                values["boll_mid"] = mid
                values["boll_upper"] = upper
                values["boll_lower"] = lower
            if settings.ma_enabled:
                for period in parse_periods(settings.ma_periods):
                    values[f"ma_{period}"] = moving_average(closes, period)
                    prev_closes = raw_closes[:-1]
                    values[f"ma_{period}_prev"] = moving_average(prev_closes, period)
                if len(raw_closes) >= 2:
                    values["prev_close"] = raw_closes[-2]
            ma250 = moving_average(closes, 250)
            if not math.isnan(ma250) and ma250 != 0:
                values["ma250"] = ma250
                values["ma250_dev"] = (price - ma250) / ma250 * 100
            for period in (20, 60, 250):
                ma_value = moving_average(closes, period)
                if not math.isnan(ma_value) and ma_value != 0:
                    values[f"ma{period}_dev"] = (price - ma_value) / ma_value * 100
            if len(highs) >= 250:
                year_high = max(highs[-250:])
                if year_high > 0:
                    values["year_high"] = year_high
                    values["yhigh_drawdown"] = (year_high - price) / year_high * 100
            atr_value = atr_percent(highs, lows, closes, 14)
            if not math.isnan(atr_value):
                values["atr_pct"] = atr_value
            breakout = breakout_text(highs, lows, price, 20)
            if breakout:
                values["breakout"] = breakout
            snapshot_dividend_yield = self._snapshot_dividend_yield(row, price)
            if snapshot_dividend_yield is not None:
                values["dividend_yield"] = snapshot_dividend_yield
            annual_dividend = self._annual_dividend_per_unit(code)
            if "dividend_yield" not in values and annual_dividend and price > 0:
                values["annual_dividend"] = annual_dividend
                values["dividend_yield"] = annual_dividend / price * 100
            values["cell_signals"] = self._cell_signals(values, settings)

            self._check_alerts(code, name, update_time, values, settings)
            self.app_queue.put(("quote", code, name, update_time, values))
            write_log(self._format_log_line(code, name, update_time, values))
        except Exception as exc:
            self.app_queue.put(("quote_error", normalize_code(item.code), str(exc)))
            write_log(f"ERROR {item.code} {exc}")

    def _chunks(self, values: list[str], size: int):
        for index in range(0, len(values), size):
            yield values[index : index + size]

    def _calculated_turnover_rate(self, code: str, row) -> float | None:
        volume = self._safe_positive_float(row.get("volume"))
        if volume is None:
            return None
        total_units = self._etf_total_units(code, row)
        if total_units is None:
            return None
        return volume / total_units * 100

    def _etf_total_units(self, code: str, row) -> float | None:
        snapshot_units = self._snapshot_total_units(row)
        if snapshot_units is not None:
            self.etf_share_cache[code] = (time.time(), snapshot_units)
            return snapshot_units
        cached = self.etf_share_cache.get(code)
        now = time.time()
        if cached and now - cached[0] < ETF_SHARE_CACHE_TTL_SECONDS:
            return cached[1] or None
        with self.etf_share_lock:
            if code not in self.etf_share_pending:
                self.etf_share_pending.add(code)
                self.etf_share_queue.append(code)
        return cached[1] if cached and cached[1] else None

    def _snapshot_total_units(self, row) -> float | None:
        for key in (
            "trust_outstanding_units",
            "outstanding_shares",
            "issued_shares",
            "total_shares",
            "circulating_shares",
        ):
            value = self._safe_positive_float(row.get(key))
            if value is not None:
                return value
        return None

    def _snapshot_dividend_yield(self, row, price: float) -> float | None:
        for key in ("dividend_ratio_ttm", "dividend_lfy_ratio", "trust_dividend_yield"):
            value = self._safe_positive_float(row.get(key))
            if value is not None:
                return value
        dividend_amount = self._safe_positive_float(row.get("dividend_ttm")) or self._safe_positive_float(row.get("dividend_lfy"))
        if dividend_amount is not None and price > 0:
            return dividend_amount / price * 100
        return None

    def _snapshot_premium_rate(self, row, price: float) -> float | None:
        premium = self._safe_float(row.get("trust_premium"))
        if premium is not None:
            return premium
        nav = self._safe_positive_float(row.get("trust_netAssetValue"))
        if nav is not None and price > 0:
            return (price - nav) / nav * 100
        return None

    def _safe_positive_float(self, value) -> float | None:
        try:
            numeric = float(value)
            if math.isnan(numeric) or numeric <= 0:
                return None
            return numeric
        except Exception:
            return None

    def _safe_float(self, value) -> float | None:
        try:
            numeric = float(value)
            if math.isnan(numeric):
                return None
            return numeric
        except Exception:
            return None

    def _annual_dividend_per_unit(self, code: str) -> float | None:
        cached = self.dividend_cache.get(code)
        now = time.time()
        if cached and now - cached[0] < 6 * 60 * 60:
            return cached[1] or None
        with self.dividend_lock:
            if code not in self.dividend_pending:
                self.dividend_pending.add(code)
                self.dividend_queue.append(code)
        return cached[1] if cached and cached[1] else None

    def _ensure_dividend_worker(self) -> None:
        if self.dividend_worker and self.dividend_worker.is_alive():
            return
        self.dividend_worker = threading.Thread(target=self._dividend_worker_loop, daemon=True)
        self.dividend_worker.start()

    def _dividend_worker_loop(self) -> None:
        ctx = None
        try:
            ctx = OpenQuoteContext(host="127.0.0.1", port=11111)
            while not self.stop_event.is_set():
                code = None
                with self.dividend_lock:
                    if self.dividend_queue:
                        code = self.dividend_queue.popleft()
                if not code:
                    self.stop_event.wait(1)
                    continue
                if self.dividend_limiter.wait(self.stop_event):
                    self._refresh_dividend_cache(ctx, code)
        except Exception as exc:
            write_log(f"ERROR dividend worker {exc}")
        finally:
            if ctx:
                ctx.close()

    def _refresh_dividend_cache(self, ctx: OpenQuoteContext, code: str) -> None:
        try:
            ret, data = ctx.get_corporate_actions_dividends(code)
            if ret != RET_OK:
                raise RuntimeError(str(data))
            dividend_list = data.get("dividend_list", []) if isinstance(data, dict) else []
            annual_dividend = self._sum_recent_dividends(dividend_list)
            if not annual_dividend:
                annual_dividend = self._sum_recent_dividends(fetch_eastmoney_fund_dividends(code))
            self.dividend_cache[code] = (time.time(), annual_dividend or 0.0)
        except Exception as exc:
            self.dividend_cache[code] = (time.time(), 0.0)
            write_log(f"ERROR dividend {code} {exc}")
        finally:
            with self.dividend_lock:
                self.dividend_pending.discard(code)

    def _capital_net_inflow(self, code: str) -> float | None:
        cached = self.capital_flow_cache.get(code)
        now = time.time()
        if cached and now - cached[0] < CAPITAL_FLOW_CACHE_TTL_SECONDS:
            return cached[1]
        with self.capital_flow_lock:
            if code not in self.capital_flow_pending:
                self.capital_flow_pending.add(code)
                self.capital_flow_queue.append(code)
        return cached[1] if cached else None

    def _ensure_capital_flow_worker(self) -> None:
        if self.capital_flow_worker and self.capital_flow_worker.is_alive():
            return
        self.capital_flow_worker = threading.Thread(target=self._capital_flow_worker_loop, daemon=True)
        self.capital_flow_worker.start()

    def _capital_flow_worker_loop(self) -> None:
        ctx = None
        try:
            ctx = OpenQuoteContext(host="127.0.0.1", port=11111)
            while not self.stop_event.is_set():
                code = None
                with self.capital_flow_lock:
                    if self.capital_flow_queue:
                        code = self.capital_flow_queue.popleft()
                if not code:
                    self.stop_event.wait(1)
                    continue
                if self.capital_flow_limiter.wait(self.stop_event):
                    self._refresh_capital_flow_cache(ctx, code)
        except Exception as exc:
            write_log(f"ERROR capital flow worker {exc}")
        finally:
            if ctx:
                ctx.close()

    def _refresh_capital_flow_cache(self, ctx: OpenQuoteContext, code: str) -> None:
        try:
            ret, data = ctx.get_capital_flow(code)
            if ret != RET_OK:
                raise RuntimeError(str(data))
            value = self._latest_capital_inflow(data)
            self.capital_flow_cache[code] = (time.time(), value)
        except Exception as exc:
            self.capital_flow_cache[code] = (time.time(), 0.0)
            write_log(f"ERROR capital flow {code} {exc}")
        finally:
            with self.capital_flow_lock:
                self.capital_flow_pending.discard(code)

    def _ensure_etf_share_worker(self) -> None:
        if self.etf_share_worker and self.etf_share_worker.is_alive():
            return
        self.etf_share_worker = threading.Thread(target=self._etf_share_worker_loop, daemon=True)
        self.etf_share_worker.start()

    def _etf_share_worker_loop(self) -> None:
        try:
            while not self.stop_event.is_set():
                code = None
                with self.etf_share_lock:
                    if self.etf_share_queue:
                        code = self.etf_share_queue.popleft()
                if not code:
                    self.stop_event.wait(1)
                    continue
                if self.etf_share_limiter.wait(self.stop_event):
                    self._refresh_etf_share_cache(code)
        except Exception as exc:
            write_log(f"ERROR ETF share worker {exc}")

    def _refresh_etf_share_cache(self, code: str) -> None:
        try:
            total_units = fetch_external_etf_total_units(code)
            self.etf_share_cache[code] = (time.time(), total_units or 0.0)
        except Exception as exc:
            self.etf_share_cache[code] = (time.time(), 0.0)
            write_log(f"ERROR ETF share {code} {exc}")
        finally:
            with self.etf_share_lock:
                self.etf_share_pending.discard(code)

    def _latest_capital_inflow(self, data) -> float:
        if data is None or not hasattr(data, "empty") or data.empty or "in_flow" not in data.columns:
            return 0.0
        value = self._safe_float(data.iloc[-1].get("in_flow"))
        return value if value is not None else 0.0

    def _sum_recent_dividends(self, dividend_list: list[dict]) -> float | None:
        cutoff = datetime.now() - timedelta(days=365)
        recent_amounts: list[float] = []
        fallback_amounts: list[float] = []
        for item in dividend_list:
            amount = parse_cash_dividend_per_unit(str(item.get("statement", "")))
            if not amount or amount <= 0:
                continue
            fallback_amounts.append(amount)
            date_text = item.get("ex_date") or item.get("dividend_payable_date") or item.get("pub_date") or ""
            action_date = parse_dividend_date(str(date_text))
            if action_date and action_date >= cutoff:
                recent_amounts.append(amount)
        if recent_amounts:
            return sum(recent_amounts)
        if fallback_amounts:
            return fallback_amounts[0]
        return None

    def _price_decimals(self, row) -> int:
        candidates = [row.get("last_price", ""), row.get("price_spread", "")]
        decimals = 0
        for value in candidates:
            text = str(value).strip()
            if "e" in text.lower():
                text = f"{float(value):.10f}".rstrip("0")
            if "." in text:
                decimals = max(decimals, len(text.rstrip("0").split(".", 1)[1]))
        return min(max(decimals, 0), 6)

    def _fmt_price_like(self, value: float, decimals: int) -> str:
        return f"{value:.{decimals}f}"

    def _check_alerts(
        self,
        code: str,
        name: str,
        update_time: str,
        values: dict[str, float],
        settings: IndicatorSettings,
    ) -> None:
        checks: dict[str, tuple[bool, str, str | None]] = {}
        price = values["price"]
        price_decimals = int(values.get("price_decimals", 4))
        price_text = self._fmt_price_like(price, price_decimals)
        if settings.rsi_enabled and not math.isnan(values.get("rsi", math.nan)):
            rsi_value = values["rsi"]
            checks["rsi_low"] = (
                rsi_value <= settings.rsi_low,
                f"【买入信号】{name} {code} RSI{settings.rsi_period}={rsi_value:.2f} 小于等于 {settings.rsi_low:g}",
                "买入",
            )
            checks["rsi_high"] = (
                rsi_value >= settings.rsi_high,
                f"【卖出信号】{name} {code} RSI{settings.rsi_period}={rsi_value:.2f} 大于等于 {settings.rsi_high:g}",
                "卖出",
            )
        if settings.kdj_enabled:
            line_key = f"kdj_{settings.kdj_line.lower()}"
            line_value = values.get(line_key, math.nan)
            if not math.isnan(line_value):
                checks[f"kdj_{settings.kdj_line}_low"] = (
                    line_value < settings.kdj_low,
                    f"{name} {code} KDJ-{settings.kdj_line}={line_value:.2f} 跌破 {settings.kdj_low:g}",
                    None,
                )
                checks[f"kdj_{settings.kdj_line}_high"] = (
                    line_value > settings.kdj_high,
                    f"{name} {code} KDJ-{settings.kdj_line}={line_value:.2f} 突破 {settings.kdj_high:g}",
                    None,
                )
        if settings.boll_enabled:
            lower = values.get("boll_lower", math.nan)
            upper = values.get("boll_upper", math.nan)
            if settings.boll_touch_lower and not math.isnan(lower):
                checks["boll_lower"] = (
                    price <= lower,
                    f"【买入信号】{name} {code} 现价={price_text} 跌破/触碰 BOLL 下轨={self._fmt_price_like(lower, price_decimals)}",
                    "买入",
                )
            if settings.boll_touch_upper and not math.isnan(upper):
                checks["boll_upper"] = (
                    price >= upper,
                    f"【卖出信号】{name} {code} 现价={price_text} 突破/触碰 BOLL 上轨={self._fmt_price_like(upper, price_decimals)}",
                    "卖出",
                )
        if settings.ma_enabled:
            prev_close = values.get("prev_close", math.nan)
            for period in parse_periods(settings.ma_periods):
                ma_now = values.get(f"ma_{period}", math.nan)
                ma_prev = values.get(f"ma_{period}_prev", math.nan)
                if math.isnan(prev_close) or math.isnan(ma_now) or math.isnan(ma_prev):
                    continue
                if settings.ma_cross_up_action != "不提示":
                    signal = settings.ma_cross_up_action
                    checks[f"ma_{period}_up"] = (
                        prev_close <= ma_prev and price >= ma_now,
                        f"【{signal}信号】{name} {code} 现价={price_text} 上穿 MA{period}={self._fmt_price_like(ma_now, price_decimals)}",
                        signal,
                    )
                if settings.ma_cross_down_action != "不提示":
                    signal = settings.ma_cross_down_action
                    checks[f"ma_{period}_down"] = (
                        prev_close >= ma_prev and price <= ma_now,
                        f"【{signal}信号】{name} {code} 现价={price_text} 下穿 MA{period}={self._fmt_price_like(ma_now, price_decimals)}",
                        signal,
                    )

        grouped: dict[str, list[tuple[str, str]]] = {"买入": [], "卖出": []}
        for key, (hit, message, side) in checks.items():
            if hit and side in grouped:
                grouped[side].append((key, message))

        for side, hits in grouped.items():
            state_key = f"{code}:{side}"
            if not hits:
                self.active_signal_keys.pop(state_key, None)
                continue
            signature = ",".join(sorted(key for key, _message in hits))
            cooldown_key = f"{state_key}:{signature}"
            if not self._alert_cooldown_ready(cooldown_key):
                self.active_signal_keys[state_key] = signature
                continue
            self.active_signal_keys[state_key] = signature
            level = self._signal_level(side, len(hits))
            details = "\n".join(f"- {message}" for _key, message in hits)
            message = f"【{level}】{name} {code} 同时满足 {len(hits)} 个条件\n{details}"
            self.alert_manager.trigger(message + f"\n更新时间：{update_time}")
            self.app_queue.put(
                (
                    "signal",
                    datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                    level,
                    code,
                    name,
                    message,
                    update_time,
                )
            )
            self._mark_alert_sent(cooldown_key)

        for key, (hit, message, side) in checks.items():
            if side in {"买入", "卖出"}:
                continue
            trigger_key = f"{code}:{key}"
            if hit and self._alert_cooldown_ready(trigger_key):
                self.alert_manager.trigger(message + f"\n更新时间：{update_time}")
                self.app_queue.put(
                    (
                        "signal",
                        datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                        "提醒",
                        code,
                        name,
                        message,
                        update_time,
                    )
                )
                self.triggered.add(trigger_key)
                self._mark_alert_sent(trigger_key)
            elif not hit and trigger_key in self.triggered:
                self.triggered.remove(trigger_key)

    def _alert_cooldown_ready(self, alert_key: str) -> bool:
        last_sent = self.last_alert_at.get(alert_key, 0)
        return time.time() - last_sent >= ALERT_COOLDOWN_SECONDS

    def _mark_alert_sent(self, alert_key: str) -> None:
        self.last_alert_at[alert_key] = time.time()

    def _signal_level(self, side: str, count: int) -> str:
        if count >= 3:
            return f"超强{side}信号"
        if count == 2:
            return f"强烈{side}信号"
        return f"{side}信号"

    def _cell_signals(self, values: dict, settings: IndicatorSettings) -> dict[str, str]:
        signals: dict[str, str] = {}
        price = values["price"]
        if settings.rsi_enabled and not math.isnan(values.get("rsi", math.nan)):
            rsi_value = values["rsi"]
            if rsi_value <= settings.rsi_low:
                signals["rsi"] = "买入"
            elif rsi_value >= settings.rsi_high:
                signals["rsi"] = "卖出"
        if settings.boll_enabled:
            lower = values.get("boll_lower", math.nan)
            upper = values.get("boll_upper", math.nan)
            if settings.boll_touch_lower and not math.isnan(lower) and price <= lower:
                signals["boll"] = "买入"
            elif settings.boll_touch_upper and not math.isnan(upper) and price >= upper:
                signals["boll"] = "卖出"
        if settings.ma_enabled:
            prev_close = values.get("prev_close", math.nan)
            ma_sides: list[str] = []
            for period in parse_periods(settings.ma_periods):
                ma_now = values.get(f"ma_{period}", math.nan)
                ma_prev = values.get(f"ma_{period}_prev", math.nan)
                if math.isnan(prev_close) or math.isnan(ma_now) or math.isnan(ma_prev):
                    continue
                if (
                    settings.ma_cross_up_action != "不提示"
                    and prev_close <= ma_prev
                    and price >= ma_now
                ):
                    ma_sides.append(settings.ma_cross_up_action)
                if (
                    settings.ma_cross_down_action != "不提示"
                    and prev_close >= ma_prev
                    and price <= ma_now
                ):
                    ma_sides.append(settings.ma_cross_down_action)
            if "买入" in ma_sides and "卖出" in ma_sides:
                signals["ma"] = "买入/卖出"
            elif "买入" in ma_sides:
                signals["ma"] = "买入"
            elif "卖出" in ma_sides:
                signals["ma"] = "卖出"
        return signals

    def _format_log_line(self, code: str, name: str, update_time: str, values: dict[str, float]) -> str:
        price_decimals = int(values.get("price_decimals", 4))
        parts = [code, name, f"price={self._fmt_price_like(values['price'], price_decimals)}", f"update={update_time}"]
        for key in [
            "change_pct",
            "turnover",
            "turnover_rate",
            "volume_ratio",
            "intraday_pos",
            "premium_rate",
            "vwap_dev",
            "capital_flow",
            "bid_ask_ratio",
            "dividend_yield",
            "atr_pct",
        ]:
            if key in values and not math.isnan(values[key]):
                if key in {"turnover", "capital_flow"}:
                    parts.append(f"{key}={values[key]:.0f}")
                else:
                    parts.append(f"{key}={values[key]:.2f}")
        for key in ["rsi", "kdj_k", "kdj_d", "kdj_j", "boll_lower", "boll_mid", "boll_upper"]:
            if key in values and not math.isnan(values[key]):
                if key == "rsi":
                    parts.append(f"{key}={values[key]:.2f}")
                elif key.startswith("boll_"):
                    parts.append(f"{key}={self._fmt_price_like(values[key], price_decimals)}")
                else:
                    parts.append(f"{key}={values[key]:.4f}")
        for key in sorted(k for k in values if k.startswith("ma_") and not k.endswith("_prev")):
            if not math.isnan(values[key]):
                parts.append(f"{key}={self._fmt_price_like(values[key], price_decimals)}")
        for key in ["ma20_dev", "ma60_dev", "ma250_dev"]:
            if key in values and not math.isnan(values[key]):
                parts.append(f"{key}={values[key]:.2f}%")
        if "yhigh_drawdown" in values and not math.isnan(values["yhigh_drawdown"]):
            parts.append(f"yhigh_drawdown={values['yhigh_drawdown']:.2f}%")
        if values.get("breakout"):
            parts.append(f"breakout={values['breakout']}")
        return " ".join(parts)


class ItemDialog(tk.Toplevel):
    def __init__(self, parent: tk.Tk, item: WatchItem | None = None, default_refresh_seconds: int = 30):
        super().__init__(parent)
        self.title("股票设置")
        self.resizable(False, False)
        self.result: WatchItem | None = None
        self.item = item or WatchItem(code="", refresh_seconds=default_refresh_seconds)
        self._build()
        self.grab_set()
        self.protocol("WM_DELETE_WINDOW", self.destroy)

    def _build(self) -> None:
        pad = {"padx": 8, "pady": 4}
        frame = ttk.Frame(self, padding=12)
        frame.grid(row=0, column=0, sticky="nsew")

        self.enabled_var = tk.BooleanVar(value=self.item.enabled)
        self.code_var = tk.StringVar(value=self.item.code)
        self.name_var = tk.StringVar(value=self.item.name)
        self.refresh_seconds_var = tk.StringVar(value=str(self.item.refresh_seconds))
        ttk.Checkbutton(frame, text="启用", variable=self.enabled_var).grid(row=0, column=0, sticky="w", **pad)
        ttk.Label(frame, text="刷新秒数").grid(row=0, column=2, sticky="w", **pad)
        ttk.Entry(frame, textvariable=self.refresh_seconds_var, width=8).grid(row=0, column=3, sticky="w", **pad)
        ttk.Label(frame, text="代码").grid(row=1, column=0, sticky="w", **pad)
        code_entry = ttk.Entry(frame, textvariable=self.code_var, width=18)
        code_entry.grid(row=1, column=1, sticky="ew", **pad)
        code_entry.bind("<FocusOut>", lambda _event: self._lookup_name())
        code_entry.bind("<Return>", lambda _event: self._lookup_name())
        ttk.Label(frame, text="名称").grid(row=1, column=2, sticky="w", **pad)
        name_box = ttk.Frame(frame)
        name_box.grid(row=1, column=3, sticky="ew", **pad)
        ttk.Entry(name_box, textvariable=self.name_var, width=18).pack(side="left")
        ttk.Button(name_box, text="查询", command=self._lookup_name).pack(side="left", padx=(6, 0))

        s = self.item.settings
        self.rsi_enabled = tk.BooleanVar(value=s.rsi_enabled)
        self.rsi_period = tk.StringVar(value=str(s.rsi_period))
        self.rsi_low = tk.StringVar(value=str(s.rsi_low))
        self.rsi_high = tk.StringVar(value=str(s.rsi_high))
        ttk.Checkbutton(frame, text="RSI", variable=self.rsi_enabled).grid(row=2, column=0, sticky="w", **pad)
        ttk.Label(frame, text="周期").grid(row=2, column=1, sticky="w", **pad)
        ttk.Entry(frame, textvariable=self.rsi_period, width=8).grid(row=2, column=1, sticky="e", **pad)
        ttk.Label(frame, text="低于").grid(row=2, column=2, sticky="w", **pad)
        ttk.Entry(frame, textvariable=self.rsi_low, width=8).grid(row=2, column=2, sticky="e", **pad)
        ttk.Label(frame, text="高于").grid(row=2, column=3, sticky="w", **pad)
        ttk.Entry(frame, textvariable=self.rsi_high, width=8).grid(row=2, column=3, sticky="e", **pad)

        self.kdj_enabled = tk.BooleanVar(value=s.kdj_enabled)
        self.kdj_period = tk.StringVar(value=str(s.kdj_period))
        self.kdj_line = tk.StringVar(value=s.kdj_line)
        self.kdj_low = tk.StringVar(value=str(s.kdj_low))
        self.kdj_high = tk.StringVar(value=str(s.kdj_high))
        ttk.Checkbutton(frame, text="KDJ", variable=self.kdj_enabled).grid(row=3, column=0, sticky="w", **pad)
        ttk.Label(frame, text="周期").grid(row=3, column=1, sticky="w", **pad)
        ttk.Entry(frame, textvariable=self.kdj_period, width=8).grid(row=3, column=1, sticky="e", **pad)
        ttk.OptionMenu(frame, self.kdj_line, self.kdj_line.get(), "K", "D", "J").grid(row=3, column=2, sticky="w", **pad)
        ttk.Label(frame, text="低/高").grid(row=3, column=2, sticky="e", **pad)
        inner = ttk.Frame(frame)
        inner.grid(row=3, column=3, sticky="ew", **pad)
        ttk.Entry(inner, textvariable=self.kdj_low, width=7).pack(side="left")
        ttk.Entry(inner, textvariable=self.kdj_high, width=7).pack(side="left", padx=(6, 0))

        self.boll_enabled = tk.BooleanVar(value=s.boll_enabled)
        self.boll_period = tk.StringVar(value=str(s.boll_period))
        self.boll_mult = tk.StringVar(value=str(s.boll_mult))
        self.boll_lower = tk.BooleanVar(value=s.boll_touch_lower)
        self.boll_upper = tk.BooleanVar(value=s.boll_touch_upper)
        ttk.Checkbutton(frame, text="BOLL", variable=self.boll_enabled).grid(row=4, column=0, sticky="w", **pad)
        ttk.Label(frame, text="周期").grid(row=4, column=1, sticky="w", **pad)
        ttk.Entry(frame, textvariable=self.boll_period, width=8).grid(row=4, column=1, sticky="e", **pad)
        ttk.Label(frame, text="倍数").grid(row=4, column=2, sticky="w", **pad)
        ttk.Entry(frame, textvariable=self.boll_mult, width=8).grid(row=4, column=2, sticky="e", **pad)
        boll_checks = ttk.Frame(frame)
        boll_checks.grid(row=4, column=3, sticky="w", **pad)
        ttk.Checkbutton(boll_checks, text="下轨", variable=self.boll_lower).pack(side="left")
        ttk.Checkbutton(boll_checks, text="上轨", variable=self.boll_upper).pack(side="left")

        self.ma_enabled = tk.BooleanVar(value=s.ma_enabled)
        self.ma_periods = tk.StringVar(value=s.ma_periods)
        self.ma_cross_up_action = tk.StringVar(value=s.ma_cross_up_action)
        self.ma_cross_down_action = tk.StringVar(value=s.ma_cross_down_action)
        ttk.Checkbutton(frame, text="MA", variable=self.ma_enabled).grid(row=5, column=0, sticky="w", **pad)
        ttk.Label(frame, text="周期").grid(row=5, column=1, sticky="w", **pad)
        ttk.Entry(frame, textvariable=self.ma_periods, width=18).grid(row=5, column=1, sticky="e", **pad)
        ma_actions = ttk.Frame(frame)
        ma_actions.grid(row=5, column=2, columnspan=2, sticky="w", **pad)
        ttk.Label(ma_actions, text="上穿").pack(side="left")
        ttk.OptionMenu(ma_actions, self.ma_cross_up_action, self.ma_cross_up_action.get(), "买入", "卖出", "不提示").pack(side="left", padx=(4, 12))
        ttk.Label(ma_actions, text="下穿").pack(side="left")
        ttk.OptionMenu(ma_actions, self.ma_cross_down_action, self.ma_cross_down_action.get(), "买入", "卖出", "不提示").pack(side="left", padx=(4, 0))

        buttons = ttk.Frame(frame)
        buttons.grid(row=6, column=0, columnspan=4, sticky="e", pady=(12, 0))
        ttk.Button(buttons, text="取消", command=self.destroy).pack(side="right", padx=(8, 0))
        ttk.Button(buttons, text="保存", command=self._save).pack(side="right")

    def _lookup_name(self) -> None:
        code = normalize_code(self.code_var.get())
        if not code:
            return
        self.code_var.set(code)
        try:
            name = lookup_stock_name(code)
            if name:
                self.name_var.set(name)
        except Exception as exc:
            write_log(f"ERROR lookup {code} {exc}")

    def _save(self) -> None:
        try:
            settings = IndicatorSettings(
                rsi_enabled=self.rsi_enabled.get(),
                rsi_period=int(self.rsi_period.get()),
                rsi_low=float(self.rsi_low.get()),
                rsi_high=float(self.rsi_high.get()),
                kdj_enabled=self.kdj_enabled.get(),
                kdj_period=int(self.kdj_period.get()),
                kdj_low=float(self.kdj_low.get()),
                kdj_high=float(self.kdj_high.get()),
                kdj_line=self.kdj_line.get(),
                boll_enabled=self.boll_enabled.get(),
                boll_period=int(self.boll_period.get()),
                boll_mult=float(self.boll_mult.get()),
                boll_touch_lower=self.boll_lower.get(),
                boll_touch_upper=self.boll_upper.get(),
                ma_enabled=self.ma_enabled.get(),
                ma_periods=",".join(str(x) for x in parse_periods(self.ma_periods.get())),
                ma_cross_up_action=self.ma_cross_up_action.get(),
                ma_cross_down_action=self.ma_cross_down_action.get(),
            )
            code = normalize_code(self.code_var.get())
            if not code:
                raise ValueError("代码不能为空")
            name = self.name_var.get().strip()
            if not name:
                try:
                    name = lookup_stock_name(code)
                except Exception as exc:
                    write_log(f"ERROR lookup {code} {exc}")
            self.result = WatchItem(
                code=code,
                name=name,
                enabled=self.enabled_var.get(),
                refresh_seconds=max(1, int(self.refresh_seconds_var.get())),
                settings=settings,
            )
            self.destroy()
        except Exception as exc:
            messagebox.showerror("设置错误", str(exc), parent=self)


class StockWatchApp:
    def __init__(self) -> None:
        self.root = tk.Tk()
        self.root.title("Futu 指标盯盘")
        self.root.geometry("1120x680")
        self.root.minsize(980, 580)
        self.config = load_config()
        self.app_queue: queue.Queue = queue.Queue()
        self.alert_manager = AlertManager(self.config.popup_enabled, self.config.sound_enabled)
        self.monitor: MonitorThread | None = None
        self.quote_rows: dict[str, str] = {}
        self.quote_sort_column: str | None = None
        self.quote_sort_reverse = False
        self.quote_headings: dict[str, str] = {}
        self.quote_header_menu_vars: dict[str, tk.BooleanVar] = {}
        self.quote_drag_column: str | None = None
        self.quote_drag_x = 0
        self.suppress_next_quote_sort = False
        self._build_ui()
        self._load_items()
        self.root.after(500, self._drain_queue)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    def _build_ui(self) -> None:
        style = ttk.Style()
        style.theme_use("clam")

        top = ttk.Frame(self.root, padding=(12, 10))
        top.pack(fill="x")
        ttk.Label(top, text="默认刷新秒数").pack(side="left")
        self.interval_var = tk.StringVar(value=str(self.config.interval_seconds))
        ttk.Spinbox(top, from_=1, to=600, textvariable=self.interval_var, width=6).pack(side="left", padx=(6, 16))
        self.popup_var = tk.BooleanVar(value=self.config.popup_enabled)
        self.sound_var = tk.BooleanVar(value=self.config.sound_enabled)
        ttk.Checkbutton(top, text="弹窗", variable=self.popup_var, command=self._save_options).pack(side="left", padx=(0, 10))
        ttk.Checkbutton(top, text="提示音", variable=self.sound_var, command=self._save_options).pack(side="left", padx=(0, 18))
        self.start_button = ttk.Button(top, text="开始盯盘", command=self._start_monitor)
        self.start_button.pack(side="left")
        self.stop_button = ttk.Button(top, text="停止", command=self._stop_monitor, state="disabled")
        self.stop_button.pack(side="left", padx=(8, 0))
        ttk.Button(top, text="测试提醒", command=self._test_alert).pack(side="left", padx=(8, 0))
        ttk.Button(top, text="显示列", command=self._choose_display_columns).pack(side="left", padx=(8, 0))
        self.status_var = tk.StringVar(value="未启动")
        ttk.Label(top, textvariable=self.status_var).pack(side="right")

        body = ttk.Frame(self.root, padding=(12, 0, 12, 12))
        body.pack(fill="both", expand=True)

        main_panes = ttk.PanedWindow(body, orient=tk.HORIZONTAL)
        main_panes.pack(fill="both", expand=True)

        left = ttk.Frame(main_panes)
        main_panes.add(left, weight=1)
        item_buttons = ttk.Frame(left)
        item_buttons.pack(fill="x", pady=(0, 8))
        ttk.Button(item_buttons, text="添加", command=self._add_item).pack(side="left")
        ttk.Button(item_buttons, text="编辑", command=self._edit_item).pack(side="left", padx=(6, 0))
        ttk.Button(item_buttons, text="删除", command=self._delete_item).pack(side="left", padx=(6, 0))

        columns = ("enabled", "code", "name", "refresh", "rules")
        self.items_tree = ttk.Treeview(left, columns=columns, show="headings", height=22)
        self.items_tree.heading("enabled", text="启用")
        self.items_tree.heading("code", text="代码")
        self.items_tree.heading("name", text="名称")
        self.items_tree.heading("refresh", text="刷新")
        self.items_tree.heading("rules", text="规则")
        self.items_tree.column("enabled", width=48, anchor="center")
        self.items_tree.column("code", width=110)
        self.items_tree.column("name", width=150)
        self.items_tree.column("refresh", width=58, anchor="center")
        self.items_tree.column("rules", width=260)
        self.items_tree.pack(fill="y", expand=True)
        self.items_tree.bind("<Double-1>", self._on_item_double_click)

        right = ttk.Frame(main_panes)
        main_panes.add(right, weight=3)
        right_panes = ttk.PanedWindow(right, orient=tk.VERTICAL)
        right_panes.pack(fill="both", expand=True)

        quote_frame = ttk.LabelFrame(right_panes, text="实时状态")
        right_panes.add(quote_frame, weight=4)
        self.quote_columns = QUOTE_COLUMNS
        quote_columns = self.quote_columns
        self.quote_tree = ttk.Treeview(quote_frame, columns=quote_columns, show="headings", height=12)
        self.quote_headings = {
            "code": "代码",
            "name": "名称",
            "price": "现价",
            "change_pct": "涨跌幅",
            "turnover": "成交额",
            "turnover_rate": "换手率",
            "volume_ratio": "量比",
            "intraday_pos": "日内位置",
            "premium_rate": "折溢价",
            "vwap_dev": "VWAP偏离",
            "capital_flow": "净流入",
            "bid_ask_ratio": "委比",
            "dividend_yield": "股息率",
            "rsi": "RSI",
            "kdj": "KDJ",
            "boll": "BOLL",
            "ma": "MA",
            "ma_dev": "均线偏离",
            "yhigh_drawdown": "年高回撤",
            "atr_pct": "ATR",
            "breakout": "突破",
            "update": "更新时间",
            "status": "状态",
        }
        widths = {
            "code": 100,
            "name": 150,
            "price": 80,
            "change_pct": 78,
            "turnover": 92,
            "turnover_rate": 78,
            "volume_ratio": 70,
            "intraday_pos": 78,
            "premium_rate": 78,
            "vwap_dev": 82,
            "capital_flow": 92,
            "bid_ask_ratio": 70,
            "dividend_yield": 80,
            "rsi": 90,
            "kdj": 150,
            "boll": 230,
            "ma": 260,
            "ma_dev": 210,
            "yhigh_drawdown": 82,
            "atr_pct": 70,
            "breakout": 80,
            "update": 150,
            "status": 180,
        }
        for col in quote_columns:
            self.quote_tree.heading(col, text=self.quote_headings[col], command=lambda column=col: self._sort_quote_rows(column))
            width = int(self.config.quote_column_widths.get(col, widths[col]))
            self.quote_tree.column(col, width=width, anchor="w")
        self._apply_display_columns()
        self.quote_tree.pack(fill="both", expand=True, padx=4, pady=4)
        self.quote_tree.tag_configure("buy", background="#e7f5ec", foreground="#146c43")
        self.quote_tree.tag_configure("sell", background="#fdecec", foreground="#b02a37")
        self.quote_tree.tag_configure("mixed", background="#fff4d6", foreground="#7a4b00")
        self.quote_tree.bind("<Button-3>", self._show_quote_header_menu)
        self.quote_tree.bind("<ButtonPress-1>", self._start_quote_header_drag)
        self.quote_tree.bind("<ButtonRelease-1>", self._finish_quote_header_drag, add="+")

        signal_frame = ttk.LabelFrame(right_panes, text="买入/卖出信号记录")
        right_panes.add(signal_frame, weight=2)
        signal_tools = ttk.Frame(signal_frame)
        signal_tools.pack(fill="x", padx=4, pady=(4, 0))
        ttk.Button(signal_tools, text="清空记录", command=self._clear_signal_rows).pack(side="right")
        signal_columns = ("time", "signal", "code", "name", "condition", "quote_time")
        self.signal_tree = ttk.Treeview(signal_frame, columns=signal_columns, show="headings", height=7)
        signal_headings = {
            "time": "提示时间",
            "signal": "方向",
            "code": "代码",
            "name": "名称",
            "condition": "触发条件",
            "quote_time": "行情时间",
        }
        signal_widths = {"time": 150, "signal": 60, "code": 90, "name": 130, "condition": 390, "quote_time": 150}
        for col in signal_columns:
            self.signal_tree.heading(col, text=signal_headings[col])
            self.signal_tree.column(col, width=signal_widths[col], anchor="w")
        self.signal_tree.pack(fill="both", expand=True, padx=4, pady=4)

        log_frame = ttk.LabelFrame(right_panes, text="运行日志")
        right_panes.add(log_frame, weight=1)
        self.log_text = tk.Text(log_frame, height=8, wrap="word")
        self.log_text.pack(fill="both", expand=True)

    def _load_items(self) -> None:
        for row in self.items_tree.get_children():
            self.items_tree.delete(row)
        for index, item in enumerate(self.config.items):
            self.items_tree.insert(
                "",
                "end",
                iid=str(index),
                values=(
                    "是" if item.enabled else "否",
                    item.code,
                    item.name,
                    f"{item.refresh_seconds}s",
                    self._rules_summary(item.settings),
                ),
            )

    def _rules_summary(self, settings: IndicatorSettings) -> str:
        rules = []
        if settings.rsi_enabled:
            rules.append(f"RSI{settings.rsi_period}<{settings.rsi_low:g}/>{settings.rsi_high:g}")
        if settings.kdj_enabled:
            rules.append(f"KDJ{settings.kdj_period}-{settings.kdj_line}<{settings.kdj_low:g}/>{settings.kdj_high:g}")
        if settings.boll_enabled:
            tracks = []
            if settings.boll_touch_lower:
                tracks.append("下")
            if settings.boll_touch_upper:
                tracks.append("上")
            rules.append(f"BOLL{settings.boll_period},{settings.boll_mult:g}触碰{''.join(tracks)}轨")
        if settings.ma_enabled:
            rules.append(
                f"MA{settings.ma_periods} 上穿{settings.ma_cross_up_action}/下穿{settings.ma_cross_down_action}"
            )
        return "；".join(rules)

    def _selected_index(self) -> int | None:
        selected = self.items_tree.selection()
        if not selected:
            return None
        return int(selected[0])

    def _add_item(self) -> None:
        dialog = ItemDialog(self.root, default_refresh_seconds=max(1, int(self.interval_var.get() or 30)))
        self.root.wait_window(dialog)
        if dialog.result:
            self.config.items.append(dialog.result)
            self._persist_and_refresh()

    def _edit_item(self) -> None:
        index = self._selected_index()
        if index is None:
            messagebox.showinfo("提示", "先选择一行")
            return
        dialog = ItemDialog(self.root, self.config.items[index], default_refresh_seconds=max(1, int(self.interval_var.get() or 30)))
        self.root.wait_window(dialog)
        if dialog.result:
            self.config.items[index] = dialog.result
            self._persist_and_refresh()

    def _on_item_double_click(self, _event) -> None:
        if self._selected_index() is not None:
            self._edit_item()

    def _delete_item(self) -> None:
        index = self._selected_index()
        if index is None:
            messagebox.showinfo("提示", "先选择一行")
            return
        del self.config.items[index]
        self._persist_and_refresh()

    def _save_options(self) -> None:
        try:
            self.config.interval_seconds = max(1, int(self.interval_var.get()))
            self.interval_var.set(str(self.config.interval_seconds))
            self.config.popup_enabled = self.popup_var.get()
            self.config.sound_enabled = self.sound_var.get()
            self.config.quote_column_widths = self._current_quote_column_widths()
            seen_columns = set()
            self.config.display_columns = [
                col
                for col in self.config.display_columns
                if col in self.quote_columns and not (col in seen_columns or seen_columns.add(col))
            ]
            if not self.config.display_columns:
                self.config.display_columns = list(self.quote_columns)
            save_config(self.config)
            self.alert_manager.configure(self.config.popup_enabled, self.config.sound_enabled)
            if self.monitor:
                self.monitor.update_config(self.config)
        except Exception as exc:
            messagebox.showerror("设置错误", str(exc))

    def _current_quote_column_widths(self) -> dict[str, int]:
        if not hasattr(self, "quote_tree"):
            return dict(self.config.quote_column_widths)
        widths: dict[str, int] = {}
        for col in self.quote_columns:
            try:
                widths[col] = int(self.quote_tree.column(col, option="width"))
            except Exception:
                pass
        return widths

    def _apply_display_columns(self) -> None:
        columns = [col for col in self.config.display_columns if col in self.quote_columns]
        if not columns:
            columns = list(self.quote_columns)
        self.quote_tree.configure(displaycolumns=columns)

    def _choose_display_columns(self) -> None:
        dialog = tk.Toplevel(self.root)
        dialog.title("实时状态显示列")
        dialog.resizable(False, False)
        dialog.grab_set()
        frame = ttk.Frame(dialog, padding=12)
        frame.pack(fill="both", expand=True)
        vars_by_col: dict[str, tk.BooleanVar] = {}
        current = set(self.config.display_columns)
        for row, col in enumerate(self.quote_columns):
            var = tk.BooleanVar(value=col in current)
            vars_by_col[col] = var
            ttk.Checkbutton(frame, text=self.quote_headings[col], variable=var).grid(row=row // 3, column=row % 3, sticky="w", padx=10, pady=5)

        def save_columns() -> None:
            selected = [col for col in self.quote_columns if vars_by_col[col].get()]
            if not selected:
                messagebox.showerror("设置错误", "至少保留一列", parent=dialog)
                return
            self.config.display_columns = selected
            self._apply_display_columns()
            self._save_options()
            dialog.destroy()

        buttons = ttk.Frame(frame)
        buttons.grid(row=4, column=0, columnspan=3, sticky="e", pady=(12, 0))
        ttk.Button(buttons, text="取消", command=dialog.destroy).pack(side="right", padx=(8, 0))
        ttk.Button(buttons, text="保存", command=save_columns).pack(side="right")

    def _show_quote_header_menu(self, event) -> None:
        if self.quote_tree.identify_region(event.x, event.y) != "heading":
            return
        menu = tk.Menu(self.root, tearoff=False)
        current = set(self.config.display_columns)
        self.quote_header_menu_vars = {}
        for col in self.quote_columns:
            checked = tk.BooleanVar(value=col in current)
            self.quote_header_menu_vars[col] = checked
            menu.add_checkbutton(
                label=self.quote_headings[col],
                variable=checked,
                command=lambda column=col: self._toggle_quote_column(column),
            )
        menu.tk_popup(event.x_root, event.y_root)

    def _toggle_quote_column(self, column: str) -> None:
        columns = [col for col in self.config.display_columns if col in self.quote_columns]
        if column in columns:
            if len(columns) == 1:
                messagebox.showinfo("提示", "至少保留一列")
                return
            columns.remove(column)
        else:
            columns.append(column)
            columns = [col for col in self.quote_columns if col in columns]
        self.config.display_columns = columns
        self._apply_display_columns()
        self._save_options()

    def _start_quote_header_drag(self, event) -> None:
        self.quote_drag_column = None
        if self.quote_tree.identify_region(event.x, event.y) != "heading":
            return
        column_id = self.quote_tree.identify_column(event.x)
        display_columns = self._current_display_columns()
        try:
            column = display_columns[int(column_id[1:]) - 1]
        except Exception:
            return
        self.quote_drag_column = column
        self.quote_drag_x = event.x

    def _finish_quote_header_drag(self, event) -> None:
        source = self.quote_drag_column
        self.quote_drag_column = None
        if not source:
            return
        if self.quote_tree.identify_region(event.x, event.y) != "heading":
            return
        if abs(event.x - self.quote_drag_x) < 8:
            return
        target_id = self.quote_tree.identify_column(event.x)
        display_columns = self._current_display_columns()
        try:
            target = display_columns[int(target_id[1:]) - 1]
        except Exception:
            return
        if source == target:
            return
        reordered = [col for col in display_columns if col != source]
        target_index = reordered.index(target)
        if event.x > self.quote_drag_x:
            target_index += 1
        reordered.insert(target_index, source)
        self.config.display_columns = reordered
        self._apply_display_columns()
        self._save_options()
        self.suppress_next_quote_sort = True

    def _current_display_columns(self) -> list[str]:
        columns = [col for col in self.config.display_columns if col in self.quote_columns]
        return columns or list(self.quote_columns)

    def _persist_and_refresh(self) -> None:
        self._save_options()
        self._load_items()
        if self.monitor:
            self.monitor.update_config(self.config)

    def _start_monitor(self) -> None:
        self._save_options()
        if self.monitor:
            return
        self.monitor = MonitorThread(self.app_queue, self.alert_manager)
        self.monitor.update_config(self.config)
        self.monitor.start()
        self.start_button.configure(state="disabled")
        self.stop_button.configure(state="normal")
        self.status_var.set("盯盘中")

    def _stop_monitor(self) -> None:
        if self.monitor:
            self.monitor.stop()
            self.monitor = None
        self.start_button.configure(state="normal")
        self.stop_button.configure(state="disabled")
        self.status_var.set("已停止")

    def _test_alert(self) -> None:
        self.alert_manager.configure(self.popup_var.get(), self.sound_var.get())
        self.alert_manager.trigger("测试提醒：关闭弹窗后，提示音会停止。")

    def _drain_queue(self) -> None:
        try:
            while True:
                event = self.app_queue.get_nowait()
                self._handle_event(event)
        except queue.Empty:
            pass
        self.root.after(500, self._drain_queue)

    def _handle_event(self, event: tuple) -> None:
        kind = event[0]
        if kind == "status":
            self.status_var.set(event[1])
            self._append_log(event[1])
        elif kind == "quote":
            _, code, name, update_time, values = event
            self._update_quote_row(code, name, update_time, values, "正常")
        elif kind == "quote_error":
            _, code, error = event
            self._update_quote_row(code, "", "", {}, error)
            self._append_log(f"{code} 错误：{error}")
        elif kind == "signal":
            _, signal_time, signal_type, code, name, message, quote_time = event
            self._add_signal_row(signal_time, signal_type, code, name, message, quote_time)
            self._append_log(f"{signal_type} {code} {message}")

    def _update_quote_row(self, code: str, name: str, update_time: str, values: dict, status: str) -> None:
        price_decimals = int(values.get("price_decimals", 4))
        cell_signals = values.get("cell_signals", {}) or {}
        price = self._fmt(values.get("price"), price_decimals)
        change_pct = self._fmt_signed_percent(values.get("change_pct"))
        turnover = self._fmt_amount(values.get("turnover"))
        turnover_rate = self._fmt_percent(values.get("turnover_rate"))
        volume_ratio = self._fmt(values.get("volume_ratio"), 2)
        intraday_pos = self._fmt_percent(values.get("intraday_pos"), 0)
        premium_rate = self._fmt_signed_percent(values.get("premium_rate"))
        vwap_dev = self._fmt_signed_percent(values.get("vwap_dev"))
        capital_flow = self._fmt_signed_amount(values.get("capital_flow"))
        bid_ask_ratio = self._fmt_signed_percent(values.get("bid_ask_ratio"))
        dividend_yield = self._fmt_percent(values.get("dividend_yield"))
        ma_dev = self._fmt_ma_devs(values)
        yhigh_drawdown = self._fmt_percent(values.get("yhigh_drawdown"))
        atr_pct = self._fmt_percent(values.get("atr_pct"))
        breakout = str(values.get("breakout", ""))
        rsi_text = self._with_cell_signal(self._fmt(values.get("rsi"), 2), cell_signals.get("rsi"))
        kdj_text = ""
        if "kdj_k" in values:
            kdj_text = f"K {self._fmt(values.get('kdj_k'))} D {self._fmt(values.get('kdj_d'))} J {self._fmt(values.get('kdj_j'))}"
        boll_text = ""
        if "boll_lower" in values:
            boll_text = (
                f"L {self._fmt(values.get('boll_lower'), price_decimals)} "
                f"M {self._fmt(values.get('boll_mid'), price_decimals)} "
                f"U {self._fmt(values.get('boll_upper'), price_decimals)}"
            )
            boll_text = self._with_cell_signal(boll_text, cell_signals.get("boll"))
        ma_items = []
        for key in sorted((k for k in values if k.startswith("ma_") and not k.endswith("_prev")), key=self._ma_sort_key):
            period = key.split("_", 1)[1]
            ma_items.append(f"MA{period} {self._fmt(values.get(key), price_decimals)}")
        ma_text = self._with_cell_signal(" ".join(ma_items), cell_signals.get("ma"))
        row_tag = self._row_signal_tag(cell_signals)
        row_values = (
            code,
            name,
            price,
            change_pct,
            turnover,
            turnover_rate,
            volume_ratio,
            intraday_pos,
            premium_rate,
            vwap_dev,
            capital_flow,
            bid_ask_ratio,
            dividend_yield,
            rsi_text,
            kdj_text,
            boll_text,
            ma_text,
            ma_dev,
            yhigh_drawdown,
            atr_pct,
            breakout,
            update_time,
            status,
        )
        if code in self.quote_rows:
            self.quote_tree.item(self.quote_rows[code], values=row_values, tags=(row_tag,) if row_tag else ())
        else:
            row_id = self.quote_tree.insert("", "end", values=row_values, tags=(row_tag,) if row_tag else ())
            self.quote_rows[code] = row_id
        self._apply_quote_sort()

    def _with_cell_signal(self, text: str, signal: str | None) -> str:
        if not text or not signal:
            return text
        return f"{text} [{signal}]"

    def _row_signal_tag(self, cell_signals: dict) -> str:
        sides = set(cell_signals.values())
        if not sides:
            return ""
        if any("买入" in side for side in sides) and any("卖出" in side for side in sides):
            return "mixed"
        if any("买入" in side for side in sides):
            return "buy"
        if any("卖出" in side for side in sides):
            return "sell"
        return ""

    def _sort_quote_rows(self, column: str) -> None:
        if self.suppress_next_quote_sort:
            self.suppress_next_quote_sort = False
            return
        if self.quote_sort_column == column:
            self.quote_sort_reverse = not self.quote_sort_reverse
        else:
            self.quote_sort_column = column
            self.quote_sort_reverse = True if column in self._numeric_quote_columns() else False
        self._update_quote_heading_arrows()
        self._apply_quote_sort()

    def _update_quote_heading_arrows(self) -> None:
        for col, label in self.quote_headings.items():
            suffix = ""
            if self.quote_sort_column == col:
                suffix = " ▼" if self.quote_sort_reverse else " ▲"
            self.quote_tree.heading(col, text=label + suffix, command=lambda column=col: self._sort_quote_rows(column))

    def _apply_quote_sort(self) -> None:
        if not self.quote_sort_column:
            return
        rows = list(self.quote_tree.get_children(""))
        rows.sort(
            key=lambda row_id: self._quote_sort_key(row_id, self.quote_sort_column or ""),
            reverse=self.quote_sort_reverse,
        )
        for index, row_id in enumerate(rows):
            self.quote_tree.move(row_id, "", index)

    def _quote_sort_key(self, row_id: str, column: str):
        value = self.quote_tree.set(row_id, column)
        if column in self._numeric_quote_columns():
            parsed = self._first_float(value)
            if parsed is None:
                return float("-inf") if self.quote_sort_reverse else float("inf")
            return parsed
        return value

    def _numeric_quote_columns(self) -> set[str]:
        return {
            "price",
            "change_pct",
            "turnover",
            "turnover_rate",
            "volume_ratio",
            "intraday_pos",
            "premium_rate",
            "vwap_dev",
            "capital_flow",
            "bid_ask_ratio",
            "dividend_yield",
            "rsi",
            "kdj",
            "boll",
            "ma",
            "ma_dev",
            "yhigh_drawdown",
            "atr_pct",
        }

    def _first_float(self, text: str) -> float | None:
        for token in text.replace(",", " ").split():
            multiplier = 1.0
            if token.endswith("亿"):
                multiplier = 100000000.0
            elif token.endswith("万"):
                multiplier = 10000.0
            token = token.strip("%亿万")
            try:
                return float(token) * multiplier
            except ValueError:
                continue
        return None

    def _ma_sort_key(self, key: str) -> int:
        try:
            return int(key.split("_", 1)[1])
        except Exception:
            return 0

    def _add_signal_row(
        self,
        signal_time: str,
        signal_type: str,
        code: str,
        name: str,
        message: str,
        quote_time: str,
    ) -> None:
        clean_message = message
        for label in [
            "买入信号",
            "强烈买入信号",
            "超强买入信号",
            "卖出信号",
            "强烈卖出信号",
            "超强卖出信号",
        ]:
            clean_message = clean_message.replace(f"【{label}】", "")
        row = (signal_time, signal_type, code, name, clean_message, quote_time)
        self.signal_tree.insert("", 0, values=row)

    def _clear_signal_rows(self) -> None:
        for row in self.signal_tree.get_children():
            self.signal_tree.delete(row)

    def _fmt(self, value, decimals: int = 4) -> str:
        if value is None:
            return ""
        try:
            if math.isnan(value):
                return ""
            return f"{float(value):.{decimals}f}"
        except Exception:
            return str(value)

    def _fmt_percent(self, value, decimals: int = 2) -> str:
        text = self._fmt(value, decimals)
        return f"{text}%" if text else ""

    def _fmt_signed_percent(self, value, decimals: int = 2) -> str:
        text = self._fmt(value, decimals)
        if not text:
            return ""
        try:
            numeric = float(value)
            return f"{numeric:+.{decimals}f}%"
        except Exception:
            return f"{text}%"

    def _fmt_amount(self, value) -> str:
        if value is None:
            return ""
        try:
            amount = float(value)
            if math.isnan(amount):
                return ""
            abs_amount = abs(amount)
            if abs_amount >= 100000000:
                return f"{amount / 100000000:.2f}亿"
            if abs_amount >= 10000:
                return f"{amount / 10000:.2f}万"
            return f"{amount:.0f}"
        except Exception:
            return str(value)

    def _fmt_signed_amount(self, value) -> str:
        text = self._fmt_amount(value)
        if not text:
            return ""
        try:
            amount = float(value)
            if amount > 0:
                return "+" + text
        except Exception:
            pass
        return text

    def _fmt_ma_devs(self, values: dict) -> str:
        parts = []
        for period in (20, 60, 250):
            key = f"ma{period}_dev"
            text = self._fmt_signed_percent(values.get(key), 1)
            if text:
                parts.append(f"{period}:{text}")
        return " ".join(parts)

    def _append_log(self, message: str) -> None:
        self.log_text.insert("end", f"{datetime.now():%H:%M:%S} {message}\n")
        self.log_text.see("end")

    def _on_close(self) -> None:
        self._save_options()
        if self.monitor:
            self.monitor.stop()
        self.root.destroy()

    def run(self) -> None:
        self.root.mainloop()


def self_test() -> None:
    ctx = OpenQuoteContext(host="127.0.0.1", port=11111)
    try:
        code = "SH.515450"
        ctx.subscribe([code], [SubType.K_DAY], subscribe_push=False)
        ret, snap = ctx.get_market_snapshot([code])
        if ret != RET_OK:
            raise SystemExit(str(snap))
        price = float(snap.iloc[0]["last_price"])
        ret, data = ctx.get_cur_kline(code, 120, KLType.K_DAY, autype=AuType.QFQ)
        if ret != RET_OK:
            raise SystemExit(str(data))
        closes = [float(x) for x in data["close"].tolist()]
        closes[-1] = price
    finally:
        ctx.close()
    value = rsi_cn(closes, 6)
    print(f"RSI6={value:.6f}")
    if math.isnan(value) or not 0 <= value <= 100:
        raise SystemExit("RSI self-test failed")
    print("self-test ok")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    app = StockWatchApp()
    app.run()


if __name__ == "__main__":
    main()

