import argparse
import ctypes
import math
import sys
import threading
import time
import winsound
from datetime import datetime
from pathlib import Path

from futu import AuType, KLType, OpenQuoteContext, RET_OK, SubType


DEFAULT_CODE = "SH.515450"
DEFAULT_NAME = "515450"
LOG_PATH = Path(__file__).with_name("monitor_515450.log")


def log(message: str) -> None:
    line = f"{datetime.now():%Y-%m-%d %H:%M:%S} {message}"
    print(line, flush=True)
    with LOG_PATH.open("a", encoding="utf-8") as f:
        f.write(line + "\n")


def alert(message: str, popup: bool) -> None:
    log("ALERT " + message)
    if popup:
        def notify_until_closed() -> None:
            stop_sound = threading.Event()

            def sound_loop() -> None:
                while not stop_sound.is_set():
                    try:
                        winsound.Beep(1200, 450)
                        winsound.Beep(900, 450)
                    except Exception:
                        time.sleep(1)
                    stop_sound.wait(1)

            sound_thread = threading.Thread(target=sound_loop)
            sound_thread.start()
            try:
                ctypes.windll.user32.MessageBoxW(0, message, "Stock monitor alert", 0x40)
            except Exception:
                pass
            finally:
                stop_sound.set()
                sound_thread.join(timeout=2)

        threading.Thread(target=notify_until_closed).start()
    else:
        try:
            winsound.Beep(1200, 450)
            winsound.Beep(900, 450)
        except Exception:
            pass


def cn_sma(values: list[float], period: int, weight: int = 1) -> float:
    """Chinese TA SMA: Y=(M*X+(N-M)*Y')/N, used by RSI(N)."""
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


def quote_row(quote_ctx: OpenQuoteContext, code: str):
    ret, data = quote_ctx.get_market_snapshot([code])
    if ret != RET_OK:
        raise RuntimeError(str(data))
    return data.iloc[0]


def daily_closes_with_live_price(quote_ctx: OpenQuoteContext, code: str, live_price: float) -> list[float]:
    ret, data = quote_ctx.get_cur_kline(
        code,
        120,
        KLType.K_DAY,
        autype=AuType.QFQ,
    )
    if ret != RET_OK:
        raise RuntimeError(str(data))
    closes = [float(x) for x in data["close"].tolist()]
    if not closes:
        raise RuntimeError("no daily K-line data")
    closes[-1] = live_price
    return closes


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--code", default=DEFAULT_CODE)
    parser.add_argument("--interval", type=float, default=30.0)
    parser.add_argument("--rsi-period", type=int, default=6)
    parser.add_argument("--boll-period", type=int, default=20)
    parser.add_argument("--boll-mult", type=float, default=2.0)
    parser.add_argument("--popup", action="store_true")
    parser.add_argument("--once", action="store_true")
    parser.add_argument("--test-alert", action="store_true")
    args = parser.parse_args()

    if args.test_alert:
        alert(
            "测试持续提醒：红利低波50ETF南方 SH.515450 price=1.4480 "
            "touched BOLL upper=1.4473 / RSI6=81.20 above 80\n\n"
            "关闭这个弹窗后，提示音会停止。",
            popup=True,
        )
        return 0

    log(
        f"START code={args.code} interval={args.interval}s "
        f"rules=RSI{args.rsi_period}<20 or >80; BOLL({args.boll_period},{args.boll_mult}) touch"
    )

    triggered: set[str] = set()
    quote_ctx = OpenQuoteContext(host="127.0.0.1", port=11111)
    try:
        ret, sub_data = quote_ctx.subscribe([args.code], [SubType.K_DAY], subscribe_push=False)
        if ret != RET_OK:
            raise RuntimeError(f"subscribe K_DAY failed: {sub_data}")
        log(f"SUBSCRIBED K_DAY {args.code}")
        while True:
            try:
                row = quote_row(quote_ctx, args.code)
                price = float(row["last_price"])
                name = str(row.get("name", DEFAULT_NAME))
                update_time = str(row.get("update_time", ""))
                closes = daily_closes_with_live_price(quote_ctx, args.code, price)
                rsi = rsi_cn(closes, args.rsi_period)
                mid, upper, lower = boll(closes, args.boll_period, args.boll_mult)

                status = (
                    f"{args.code} {name} price={price:.4f} update={update_time} "
                    f"RSI{args.rsi_period}={rsi:.2f} "
                    f"BOLL lower={lower:.4f} mid={mid:.4f} upper={upper:.4f}"
                )
                log(status)

                checks = {
                    "rsi_below_20": (rsi < 20, f"{name} {args.code} RSI{args.rsi_period}={rsi:.2f} below 20"),
                    "rsi_above_80": (rsi > 80, f"{name} {args.code} RSI{args.rsi_period}={rsi:.2f} above 80"),
                    "touch_lower": (price <= lower, f"{name} {args.code} price={price:.4f} touched BOLL lower={lower:.4f}"),
                    "touch_upper": (price >= upper, f"{name} {args.code} price={price:.4f} touched BOLL upper={upper:.4f}"),
                }
                for key, (hit, message) in checks.items():
                    if hit and key not in triggered:
                        alert(message, args.popup)
                        triggered.add(key)
                    elif not hit and key in triggered:
                        triggered.remove(key)
                if args.once:
                    return 0
            except Exception as exc:
                log(f"ERROR {exc}")
                if args.once:
                    return 1
            time.sleep(args.interval)
    finally:
        quote_ctx.close()


if __name__ == "__main__":
    sys.exit(main())
