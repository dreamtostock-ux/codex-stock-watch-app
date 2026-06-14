import argparse
import ctypes
import html
import json
import math
import queue
import re
import threading
import time
import tkinter as tk
import urllib.request
from dataclasses import asdict, dataclass, field
from datetime import datetime, timedelta
from pathlib import Path
from tkinter import messagebox, ttk

import winsound
from futu import AuType, KLType, OpenQuoteContext, RET_OK, SubType


APP_DIR = Path(__file__).resolve().parent
CONFIG_PATH = APP_DIR / "stock_watch_config.json"
LOG_PATH = APP_DIR / "stock_watch_app.log"
QUOTE_COLUMNS = ("code", "name", "price", "dividend_yield", "rsi", "kdj", "boll", "ma", "update", "status")
DEFAULT_DISPLAY_COLUMNS = ["code", "name", "price", "dividend_yield", "rsi", "kdj", "boll", "ma", "update", "status"]


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


def migrate_display_columns(columns: list[str]) -> list[str]:
    known = set(QUOTE_COLUMNS)
    migrated = []
    inserted_dividend_yield = False
    for col in columns:
        if col not in known or col in migrated:
            continue
        migrated.append(col)
        if col == "price" and "dividend_yield" not in columns:
            migrated.append("dividend_yield")
            inserted_dividend_yield = True
    if not migrated:
        return list(DEFAULT_DISPLAY_COLUMNS)
    if not inserted_dividend_yield and "dividend_yield" not in migrated:
        insert_at = migrated.index("price") + 1 if "price" in migrated else len(migrated)
        migrated.insert(insert_at, "dividend_yield")
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
        self.subscribed: set[str] = set()
        self.last_poll_at: dict[str, float] = {}
        self.dividend_cache: dict[str, tuple[float, float]] = {}
        self.dividend_pending: set[str] = set()

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
            self.app_queue.put(("status", "已连接 Futu OpenD"))
            while not self.stop_event.is_set():
                with self.config_lock:
                    config = config_from_dict(json.loads(json.dumps(asdict(self.config), ensure_ascii=False)))
                now = time.time()
                for item in config.items:
                    if self.stop_event.is_set():
                        break
                    if item.enabled and item.code:
                        code = normalize_code(item.code)
                        interval = max(1, int(item.refresh_seconds or config.interval_seconds))
                        if now - self.last_poll_at.get(code, 0) >= interval:
                            self._poll_item(ctx, item)
                            self.last_poll_at[code] = now
                self.stop_event.wait(1)
        except Exception as exc:
            write_log(f"ERROR monitor stopped: {exc}")
            self.app_queue.put(("status", f"监控异常：{exc}"))
        finally:
            if ctx:
                ctx.close()

    def _ensure_subscribed(self, ctx: OpenQuoteContext, code: str) -> None:
        if code in self.subscribed:
            return
        ret, data = ctx.subscribe([code], [SubType.K_DAY], subscribe_push=False)
        if ret != RET_OK:
            raise RuntimeError(str(data))
        self.subscribed.add(code)

    def _poll_item(self, ctx: OpenQuoteContext, item: WatchItem) -> None:
        try:
            code = normalize_code(item.code)
            self._ensure_subscribed(ctx, code)
            ret, snap = ctx.get_market_snapshot([code])
            if ret != RET_OK:
                raise RuntimeError(str(snap))
            row = snap.iloc[0]
            price = float(row["last_price"])
            price_decimals = self._price_decimals(row)
            name = str(row.get("name", item.name or code))
            update_time = str(row.get("update_time", ""))
            ret, kline = ctx.get_cur_kline(code, 300, KLType.K_DAY, autype=AuType.QFQ)
            if ret != RET_OK:
                raise RuntimeError(str(kline))

            raw_closes = [float(x) for x in kline["close"].tolist()]
            closes = list(raw_closes)
            highs = [float(x) for x in kline["high"].tolist()]
            lows = [float(x) for x in kline["low"].tolist()]
            if closes:
                closes[-1] = price
                highs[-1] = max(highs[-1], price)
                lows[-1] = min(lows[-1], price)

            settings = item.settings
            values: dict[str, float] = {"price": price, "price_decimals": price_decimals}
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

    def _snapshot_dividend_yield(self, row, price: float) -> float | None:
        for key in ("dividend_ratio_ttm", "dividend_lfy_ratio", "trust_dividend_yield"):
            value = self._safe_positive_float(row.get(key))
            if value is not None:
                return value
        dividend_amount = self._safe_positive_float(row.get("dividend_ttm")) or self._safe_positive_float(row.get("dividend_lfy"))
        if dividend_amount is not None and price > 0:
            return dividend_amount / price * 100
        return None

    def _safe_positive_float(self, value) -> float | None:
        try:
            numeric = float(value)
            if math.isnan(numeric) or numeric <= 0:
                return None
            return numeric
        except Exception:
            return None

    def _annual_dividend_per_unit(self, code: str) -> float | None:
        cached = self.dividend_cache.get(code)
        now = time.time()
        if cached and now - cached[0] < 6 * 60 * 60:
            return cached[1] or None
        if code not in self.dividend_pending:
            self.dividend_pending.add(code)
            threading.Thread(target=self._refresh_dividend_cache, args=(code,), daemon=True).start()
        return cached[1] if cached and cached[1] else None

    def _refresh_dividend_cache(self, code: str) -> None:
        ctx = None
        try:
            ctx = OpenQuoteContext(host="127.0.0.1", port=11111)
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
            if ctx:
                ctx.close()
            self.dividend_pending.discard(code)

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
            if self.active_signal_keys.get(state_key) == signature:
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

        for key, (hit, message, side) in checks.items():
            if side in {"买入", "卖出"}:
                continue
            trigger_key = f"{code}:{key}"
            if hit and trigger_key not in self.triggered:
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
            elif not hit and trigger_key in self.triggered:
                self.triggered.remove(trigger_key)

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
            "dividend_yield": "股息率",
            "rsi": "RSI",
            "kdj": "KDJ",
            "boll": "BOLL",
            "ma": "MA",
            "update": "更新时间",
            "status": "状态",
        }
        widths = {
            "code": 100,
            "name": 150,
            "price": 80,
            "dividend_yield": 80,
            "rsi": 90,
            "kdj": 150,
            "boll": 230,
            "ma": 260,
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
        dividend_yield = self._fmt_percent(values.get("dividend_yield"))
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
        row_values = (code, name, price, dividend_yield, rsi_text, kdj_text, boll_text, ma_text, update_time, status)
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
            self.quote_sort_reverse = True if column in {"price", "dividend_yield", "rsi", "kdj", "boll", "ma"} else False
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
        if column in {"price", "dividend_yield", "rsi", "kdj", "boll", "ma"}:
            parsed = self._first_float(value)
            if parsed is None:
                return float("-inf") if self.quote_sort_reverse else float("inf")
            return parsed
        return value

    def _first_float(self, text: str) -> float | None:
        for token in text.replace(",", " ").split():
            try:
                return float(token)
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
