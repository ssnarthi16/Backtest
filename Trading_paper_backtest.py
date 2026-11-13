import base64
import copy
import hashlib
import io
import json
import math
import os
import re
import threading
import time
from dataclasses import asdict, dataclass
from datetime import datetime
from datetime import time as dtime
from pathlib import Path
from types import SimpleNamespace

import numpy as np
import pandas as pd
import requests
import streamlit as st

IST = "Asia/Kolkata"
MASTER_URL = "https://margincalculator.angelbroking.com/OpenAPI_File/files/OpenAPIScripMaster.json"
CANDLE_KEYS = ("prev_O", "prev_H", "prev_L", "prev_C", "sig_O", "sig_H", "sig_L", "sig_C")
STORE_KEYS = CANDLE_KEYS + ("hist",)          # hist = last 5 candles [O,H,L,C] (oldest -> newest) saved with every entry


# ============================== 10 CANDLE PATTERNS (same as the Google Sheet formulas) ==============================
# Sheet columns: B=Open, C=High, D=Low, E=Close.  Each function gets the pattern's candles OLDEST -> NEWEST
# (k[0] = first / "row 2" candle ... k[-1] = latest closed candle) and returns True/False (Series for a whole DataFrame).
def _body(k):
    return (k.c - k.o).abs()


def _rng(k):
    return k.h - k.l


# Word-file rule for Three White Soldiers (ENTRY RULE section)
SOLDIER_GAP_MIN = 0.995     # open >= prev_open * 0.995   (gap-down open reject)
SOLDIER_WICK_MAX = 0.30     # upper wick <= 30% of day range (near-high close)
SOLDIER_BODY_MIN = 0.20     # body >= 20% of day range       (strong body, doji reject)
TWEEZER_LOW_TOL = 0.001     # two lows count as "the same" when within 0.1%
DOWNTREND_LOOKBACK = 5      # "in a downtrend": close before the pattern < close this many candles earlier
DOWNTREND_PATTERNS = ("Bullish Engulfing", "Hammer")      # the Word file asks for a downtrend only for these two


def _p_engulf(k):       # small bearish candle completely engulfed by a large bullish candle (downtrend filter applied in detect_patterns)
    a, b = k
    return (a.o > a.c) & (b.o < b.c) & (b.o <= a.c) & (b.c >= a.o) & (_body(b) > _body(a))


def _p_harami(k):       # small bullish candle completely inside the body of the preceding large bearish candle
    a, b = k
    return (a.o > a.c) & (b.o < b.c) & (b.o > a.c) & (b.c < a.o)


def _p_marubozu(k):     # bullish, closes near its high, little/no shadow on either end
    (a,) = k
    return (a.c > a.o) & ((a.o - a.l) <= 0.05 * (a.c - a.o)) & ((a.h - a.c) <= 0.05 * (a.c - a.o))


def _p_hammer(k):       # small body at the top of the range, lower shadow >= 2x body (downtrend filter applied in detect_patterns)
    (a,) = k
    bd = _body(a)
    return ((a.h - a.l) > 0) & ((np.minimum(a.o, a.c) - a.l) >= 2 * bd) & ((a.h - np.maximum(a.o, a.c)) <= 0.1 * bd)


def _p_inv_hammer(k):   # small body at the bottom of the range, long upper shadow  +  NEXT candle closes bullish (confirmation)
    a, b = k
    bd = _body(a)
    return (((a.h - a.l) > 0) & ((a.h - np.maximum(a.o, a.c)) >= 2 * bd) & ((np.minimum(a.o, a.c) - a.l) <= 0.1 * bd)
            & (b.c > b.o))


def _p_morning(k):      # bearish, small GAP-DOWN middle candle, strong bullish 3rd candle closing past the middle of the 1st body
    a, b, c = k
    return ((a.c < a.o) & (_body(b) <= 0.5 * _body(a)) & (np.maximum(b.o, b.c) < a.c)
            & (c.c > c.o) & (_body(c) >= 0.5 * _rng(c)) & (c.c >= a.o - 0.5 * (a.o - a.c)))


def _p_piercing(k):     # bullish candle opens below the previous low, closes above the middle of the prior bearish body
    a, b = k
    return (a.c < a.o) & (b.c > b.o) & (b.o < a.l) & (b.c > a.o - (a.o - a.c) / 2) & (b.c < a.o)


def _p_rising3(k):      # long bullish, 3 small BEARISH candles inside its range, 5th bullish candle closes above the 1st candle's HIGH
    a, b, c, d, e = k
    ok = a.c > a.o
    for m in (b, c, d):
        ok = ok & (m.c < m.o) & (_body(m) <= 0.5 * _body(a)) & (m.h <= a.h) & (m.l >= a.l)
    return ok & (e.c > e.o) & (e.c > a.h)


def _p_soldiers(k):     # Word ENTRY RULE: bullish, rising closes, no gap-down open, near-high close, strong body (every candle)
    a, b, c = k
    ok = (b.c > a.c) & (c.c > b.c) & (b.o >= a.o * SOLDIER_GAP_MIN) & (c.o >= b.o * SOLDIER_GAP_MIN)
    for m in (a, b, c):
        r = _rng(m)
        ok = ok & (m.c > m.o) & (r > 0) & ((m.h - m.c) <= SOLDIER_WICK_MAX * r) & (_body(m) >= SOLDIER_BODY_MIN * r)
    return ok


def _p_tweezer(k):      # two candles share the same low, followed by a bullish confirmation candle
    a, b, c = k
    return ((b.l - a.l).abs() <= TWEEZER_LOW_TOL * a.l) & (c.c > c.o)


# (name, candles used, python check, Excel/Sheets formula builder: rows -> formula)   Excel columns: B=Open C=High D=Low E=Close
# (the downtrend condition for Engulfing / Hammer is applied in Python only - see DOWNTREND_PATTERNS)
PATTERN_DEFS = (
    ("Bullish Engulfing", 2, _p_engulf,
     lambda r: f'=IF(AND(B{r[0]}>E{r[0]},B{r[1]}<E{r[1]},B{r[1]}<=E{r[0]},E{r[1]}>=B{r[0]},ABS(E{r[1]}-B{r[1]})>ABS(E{r[0]}-B{r[0]})),"BULLISH ENGULFING ","")'),
    ("Bullish Harami", 2, _p_harami,
     lambda r: f'=IF(AND(B{r[0]}>E{r[0]},B{r[1]}<E{r[1]},B{r[1]}>E{r[0]},E{r[1]}<B{r[0]}),"BULLISH harami","")'),
    ("Bullish Marubozu", 1, _p_marubozu,
     lambda r: f'=IF(AND(E{r[0]}>B{r[0]},(B{r[0]}-D{r[0]})<=0.05*(E{r[0]}-B{r[0]}),(C{r[0]}-E{r[0]})<=0.05*(E{r[0]}-B{r[0]})),"Bullish Marubozu","")'),
    ("Hammer", 1, _p_hammer,
     lambda r: f'=IF(AND(C{r[0]}>D{r[0]},(MIN(B{r[0]},E{r[0]})-D{r[0]})>=2*ABS(E{r[0]}-B{r[0]}),(C{r[0]}-MAX(B{r[0]},E{r[0]}))<=0.1*ABS(E{r[0]}-B{r[0]})),"HAMMER","")'),
    ("Inverted Hammer", 2, _p_inv_hammer,
     lambda r: f'=IF(AND(C{r[0]}>D{r[0]},(C{r[0]}-MAX(B{r[0]},E{r[0]}))>=2*ABS(E{r[0]}-B{r[0]}),(MIN(B{r[0]},E{r[0]})-D{r[0]})<=0.1*ABS(E{r[0]}-B{r[0]}),E{r[1]}>B{r[1]}),"INVERTED HAMMER","")'),
    ("Morning Star", 3, _p_morning,
     lambda r: f'=IF(AND(E{r[0]}<B{r[0]},ABS(E{r[1]}-B{r[1]})<=0.5*ABS(E{r[0]}-B{r[0]}),MAX(B{r[1]},E{r[1]})<E{r[0]},E{r[2]}>B{r[2]},ABS(E{r[2]}-B{r[2]})>=0.5*(C{r[2]}-D{r[2]}),E{r[2]}>=B{r[0]}-0.5*(B{r[0]}-E{r[0]})),"MORNING STAR","")'),
    ("Piercing", 2, _p_piercing,
     lambda r: f'=IF(AND(E{r[0]}<B{r[0]},E{r[1]}>B{r[1]},B{r[1]}<D{r[0]},E{r[1]}>B{r[0]}-(B{r[0]}-E{r[0]})/2,E{r[1]}<B{r[0]}),"PIERCING","")'),
    ("Rising Three Methods", 5, _p_rising3,
     lambda r: (f'=IF(AND(E{r[0]}>B{r[0]},'
                + ','.join(f'E{x}<B{x},ABS(E{x}-B{x})<=0.5*ABS(E{r[0]}-B{r[0]}),C{x}<=C{r[0]},D{x}>=D{r[0]}' for x in r[1:4])
                + f',E{r[4]}>B{r[4]},E{r[4]}>C{r[0]}),"RISING THREE METHODS","")')),
    ("Three White Soldiers", 3, _p_soldiers,
     lambda r: ('=IF(AND(' + ','.join(
         f'E{x}>B{x},C{x}>D{x},(C{x}-E{x})<={SOLDIER_WICK_MAX}*(C{x}-D{x}),(E{x}-B{x})>={SOLDIER_BODY_MIN}*(C{x}-D{x})' for x in r)
         + f',E{r[1]}>E{r[0]},E{r[2]}>E{r[1]},B{r[1]}>=B{r[0]}*{SOLDIER_GAP_MIN},B{r[2]}>=B{r[1]}*{SOLDIER_GAP_MIN}),"THREE WHITE SOLDIERS","")')),
    ("Tweezer Bottom", 3, _p_tweezer,
     lambda r: f'=IF(AND(ABS(D{r[1]}-D{r[0]})<={TWEEZER_LOW_TOL}*D{r[0]},E{r[2]}>B{r[2]}),"TWEEZER BOTTOM","")'),
)
PATTERNS = tuple(d[0] for d in PATTERN_DEFS)

SL_PCT = 0.0
MAX_HOLD_DAYS = 1
TREND_LOOKBACK = 0
TWEEZER_TOL_PCT = 0.10
FUTURES_MARGIN_PCT = 10.0
BROKERAGE_PCT = 0.0
SLIPPAGE_PCT = 0.0
FRESH_SECONDS = 120
REFRESH_SECONDS = 5

TIMEFRAMES = {
    "1 minute": ("ONE_MINUTE", 1),
    "3 minutes": ("THREE_MINUTE", 3),
    "5 minutes": ("FIVE_MINUTE", 5),
    "10 minutes": ("TEN_MINUTE", 10),
    "15 minutes": ("FIFTEEN_MINUTE", 15),
    "30 minutes": ("THIRTY_MINUTE", 30),
    "1 hour": ("ONE_HOUR", 60),
    "4 hours": ("FOUR_HOUR", 240),     # built from 1-hour candles (Angel One has no 4H interval)
    "1 day": ("ONE_DAY", 1440),
}

OWNER_ID = "owner"
# Absolute data root so saves survive cwd changes on Streamlit Cloud.
# Override with env DATA_DIR if needed. App reboot on free Cloud can still wipe disk.
_DATA_DIR = os.environ.get("DATA_DIR") or os.path.join(os.path.expanduser("~"), "paper_trading_data")
STRATEGIES_ROOT = os.path.join(_DATA_DIR, "strategies")
os.makedirs(STRATEGIES_ROOT, exist_ok=True)


# ============================== CONFIG ==============================
@dataclass
class Config:
    capital: float = 100000.0
    max_open: int = 5
    target_pct: float = 1.0
    sl_pct: float = SL_PCT
    max_hold: int = MAX_HOLD_DAYS
    tweezer_tol_pct: float = TWEEZER_TOL_PCT
    trend_lookback: int = TREND_LOOKBACK
    brokerage_pct: float = BROKERAGE_PCT
    slippage_pct: float = SLIPPAGE_PCT
    interval: str = "FIVE_MINUTE"
    tf_min: int = 5
    patterns: tuple = PATTERNS
    position_amount: float = 0.0
    size_mode: str = "amount"           # "amount" | "qty" | "equal" (equal weight)
    position_qty: int = 0               # used when size_mode == "qty" (shares; lots for NFO/MCX)
    n_stocks: int = 0                   # selected stocks - equal weight divides capital by this when no max-position limit
    no_limit: bool = False
    cloud_filter: str = ""              # optional Ichimoku cloud filter: "" (off) | "Above" | "Center" | "Below"

    @property
    def per_position(self):
        if self.size_mode == "equal":
            n = max(self.n_stocks, 1) if self.no_limit else max(self.max_open, 1)
            return self.capital / n
        return self.position_amount if self.position_amount > 0 else self.capital / self.max_open

    @property
    def size_text(self):
        if self.size_mode == "qty":
            return f"qty/position {int(self.position_qty)}"
        return ("equal weight " if self.size_mode == "equal" else "amount/position ") + f"{self.per_position:,.0f}"

    def size_qty(self, one_lot, lot, cash):
        """(qty the sizing rule alone allows, qty after the free-cash cap) - in shares (lots x lot size for NFO/MCX)."""
        if self.size_mode == "qty":
            n = max(int(self.position_qty), 0)
            n_cash = math.floor(max(cash, 0) / one_lot) if one_lot > 0 else 0
            return n * lot, min(n, n_cash) * lot
        return (math.floor(self.per_position / one_lot) * lot,
                math.floor(min(self.per_position, cash) / one_lot) * lot)


def _cfg_from_data(d):
    """Config from a saved config.json dict (paper and live files)."""
    return Config(
        capital=float(d.get("capital", 0) or 0),
        max_open=int(d.get("max_open", 5)),
        target_pct=float(d.get("target_pct", 1.0)),
        sl_pct=float(d.get("sl_pct", 0) or 0),
        interval=d.get("interval", "FIVE_MINUTE"),
        tf_min=int(d.get("tf_min", 5)),
        position_amount=float(d.get("position_amount") or 0),
        size_mode=str(d.get("size_mode") or "amount"),
        position_qty=int(d.get("position_qty") or 0),
        n_stocks=len(d.get("items") or []),
        no_limit=bool(d.get("no_limit", False)),
        cloud_filter=cloud_text(d.get("cloud_filter")),
        max_hold=int(d.get("max_hold", MAX_HOLD_DAYS) or MAX_HOLD_DAYS),
        patterns=tuple(p for p in (d.get("patterns") or PATTERNS) if p in PATTERNS) or PATTERNS,
    )


# ============================== TIME ==============================
def now_ist():
    return pd.Timestamp.now(tz=IST).tz_localize(None)


def market_open(now, exchange="NSE"):
    start, end = (dtime(9, 0), dtime(23, 30)) if exchange == "MCX" else (dtime(9, 15), dtime(15, 30))
    return now.weekday() < 5 and start <= now.time() <= end


def exit_time(exchange):
    return dtime(23, 15) if exchange == "MCX" else dtime(15, 15)


def session_done(now):
    return now.weekday() < 5 and now.time() > dtime(15, 30)


# ============================== PATTERNS ==============================
def detect_patterns(df, cfg=None, downtrend=True):
    """True/False per candle for every pattern: the pattern ENDS on that candle (its last candle)."""
    o, h, l, c = (df[x].astype(float) for x in ("open", "high", "low", "close"))

    def candle(sh):
        return SimpleNamespace(o=o.shift(sh), h=h.shift(sh), l=l.shift(sh), c=c.shift(sh))

    sig = pd.DataFrame(
        {name: fn([candle(n - 1 - j) for j in range(n)]) for name, n, fn, _ in PATTERN_DEFS},
        index=df.index,
    )
    lb = int(getattr(cfg, "trend_lookback", 0) or 0)
    if lb > 0:                                              # optional extra filter for ALL patterns (off by default)
        sig = sig.mul(c.shift(1) < c.shift(lb + 1), axis=0).astype(bool)
    n_of = {name: n for name, n, _, _ in PATTERN_DEFS}
    for name in (DOWNTREND_PATTERNS if downtrend else ()):  # Word file: only these need "in a downtrend"
        if name in sig.columns:
            n = n_of[name]                                  # candle just before the pattern vs DOWNTREND_LOOKBACK candles earlier
            sig[name] = sig[name].astype(bool) & (c.shift(n) < c.shift(n + DOWNTREND_LOOKBACK)).fillna(False)
    return sig.fillna(False).astype(bool)


def classify_candles(r, only=None):
    """Re-check the candles saved with an entry (hist, or the old prev/sig pair) against the formulas."""
    hist = r.get("hist")
    if not isinstance(hist, (list, tuple)) or not hist:
        try:
            hist = [[r["prev_O"], r["prev_H"], r["prev_L"], r["prev_C"]],
                    [r["sig_O"], r["sig_H"], r["sig_L"], r["sig_C"]]]
        except (KeyError, TypeError):
            return None
    try:
        df = pd.DataFrame(hist, columns=["open", "high", "low", "close"]).astype(float)
    except (ValueError, TypeError):
        return None
    if df.empty or df.iloc[-1].isna().any():
        return None
    sig = detect_patterns(df, downtrend=False)              # saved hist is too short for the downtrend check
    names = [n for n in (only or PATTERNS) if n in sig.columns and bool(sig[n].iat[-1])]
    return " + ".join(names) if names else "No pattern"


# ============================== ICHIMOKU CLOUD (optional entry filter) ==============================
CLOUD_OPTIONS = ("Above", "Center", "Below")      # last closed candle: above the cloud / inside the cloud / below the cloud
CLOUD_LABEL = {"Above": "Above cloud", "Center": "Center (inside cloud)", "Below": "Below cloud"}
CLOUD_BY_LABEL = {v: k for k, v in CLOUD_LABEL.items()}


def cloud_list(v):
    """Saved cloud filter -> list of positions. Accepts '' / 'Above' / 'Above,Center' / a list."""
    parts = v if isinstance(v, (list, tuple, set)) else str(v or "").split(",")
    got = {str(x).strip() for x in parts}
    return [k for k in CLOUD_OPTIONS if k in got]


def cloud_text(v):
    """Canonical saved form: '' (filter off) or e.g. 'Above,Center'."""
    return ",".join(cloud_list(v))
CLOUD_MIN_BARS = 78                               # Senkou B needs 52 candles + the cloud is drawn 26 candles ahead
# calendar days of history to load when the cloud filter is ON (so the cloud has >= CLOUD_MIN_BARS candles)
CLOUD_DAYS = {"ONE_MINUTE": 5, "THREE_MINUTE": 5, "FIVE_MINUTE": 6, "TEN_MINUTE": 8, "FIFTEEN_MINUTE": 10,
              "THIRTY_MINUTE": 18, "ONE_HOUR": 35, "FOUR_HOUR": 130, "ONE_DAY": 160}


def ichimoku_cloud(df, tenkan=9, kijun=26, senkou_b=52, shift=26):
    """Standard Ichimoku (9, 26, 52, 26). Row t holds the cloud as DRAWN under candle t
       (Senkou A / B calculated `shift` candles earlier)."""
    h, l = df["high"].astype(float), df["low"].astype(float)

    def mid(n):
        return (h.rolling(n).max() + l.rolling(n).min()) / 2

    span_a = ((mid(tenkan) + mid(kijun)) / 2).shift(shift)
    span_b = mid(senkou_b).shift(shift)
    return pd.DataFrame({"span_a": span_a, "span_b": span_b,
                         "top": np.maximum(span_a, span_b), "bottom": np.minimum(span_a, span_b)}, index=df.index)


def cloud_position(df):
    """'Above' / 'Center' / 'Below' for the LAST candle's close vs the cloud, or None when there are too few candles."""
    if df is None or len(df) < CLOUD_MIN_BARS:
        return None
    last = ichimoku_cloud(df).iloc[-1]
    if pd.isna(last["top"]) or pd.isna(last["bottom"]):
        return None
    close = float(df["close"].iat[-1])
    return "Above" if close > last["top"] else "Below" if close < last["bottom"] else "Center"


# ============================== ANGEL ONE ==============================
def angel_login(api_key, client_id, mpin, totp_secret):
    try:
        import pyotp
        from SmartApi import SmartConnect
    except ImportError:
        return None, "Install first:  pip install smartapi-python pyotp"
    try:
        smart = SmartConnect(api_key=api_key.strip())
        otp = pyotp.TOTP(totp_secret.replace(" ", "").strip()).now()
        res = smart.generateSession(client_id.strip(), mpin.strip(), otp)
        if not res or not res.get("status"):
            return None, f"Login failed: {(res or {}).get('message', 'unknown error')}"
        return smart, None
    except Exception as ex:
        return None, f"Login error: {ex}"


def _to_ist_naive(series):
    return pd.to_datetime(series, utc=True).dt.tz_convert(IST).dt.tz_localize(None)


CANDLE_GAP_MIN, CANDLE_GAP_MAX = 0.36, 1.2          # Angel limit ~3 calls/sec -> start near it, back off only if it complains
CANDLE_CALL_GAP = CANDLE_GAP_MIN
_GAP_LOCK, _GAP_LAST = threading.Lock(), {}
QUOTE_BACKOFF = [0.0]


def _gap(kind, gap):
    """Minimum seconds between two calls of the same Angel API kind (all threads share it)."""
    with _GAP_LOCK:
        wait = _GAP_LAST.get(kind, 0.0) + gap - time.time()
        if wait > 0:
            time.sleep(wait)
        _GAP_LAST[kind] = time.time()


def _is_rate_err(msg):
    m = str(msg).lower()
    return "access rate" in m or "exceeding" in m or "too many" in m
_RATE_LOCK, _RATE_LAST = threading.Lock(), [0.0]


def _gap_adjust(rate_error):
    """Adaptive gap: +0.15s on every rate-limit error, shrinks slowly back to the minimum on success."""
    global CANDLE_CALL_GAP
    with _RATE_LOCK:
        if rate_error:
            CANDLE_CALL_GAP = min(CANDLE_GAP_MAX, CANDLE_CALL_GAP + 0.15)
        else:
            CANDLE_CALL_GAP = max(CANDLE_GAP_MIN, CANDLE_CALL_GAP - 0.01)


def _rate_wait():
    with _RATE_LOCK:
        wait = _RATE_LAST[0] + CANDLE_CALL_GAP - time.time()
        if wait > 0:
            time.sleep(wait)
        _RATE_LAST[0] = time.time()


def _candles(smart, item, interval, start, end):
    params = {
        "exchange": item["exchange"], "symboltoken": str(item["token"]), "interval": interval,
        "fromdate": start.strftime("%Y-%m-%d %H:%M"), "todate": end.strftime("%Y-%m-%d %H:%M"),
    }
    for _ in range(4):
        _rate_wait()
        try:
            res = smart.getCandleData(params)
        except Exception as ex_:
            res = None
            LAST_API_ERROR["candle"] = f"{type(ex_).__name__}: {ex_}"
        if res and res.get("status") and res.get("data") is not None:
            _gap_adjust(False)
            if not res["data"]:
                return pd.DataFrame()
            d = pd.DataFrame(res["data"], columns=["date", "open", "high", "low", "close", "volume"])
            d["date"] = _to_ist_naive(d["date"])
            return d
        rate_err = _is_rate_err(LAST_API_ERROR.get("candle", "")) or _is_rate_err((res or {}).get("message", ""))
        _gap_adjust(rate_err)
        time.sleep(3 if rate_err else 2)
    return pd.DataFrame()


def _resample_4h(d, exchange):
    """1-hour candles -> 4-hour candles aligned to the session start (NSE/BSE/NFO 09:15, MCX 09:00)."""
    sh, sm = (9, 0) if exchange == "MCX" else (9, 15)
    d = d.sort_values("date").copy()
    day = d["date"].dt.normalize()
    mins = (d["date"] - day).dt.total_seconds() // 60 - (sh * 60 + sm)
    d["_g"], d["_d"] = (mins // 240).astype(int), day
    out = d.groupby(["_d", "_g"], sort=True).agg(
        date=("date", "first"), open=("open", "first"), high=("high", "max"),
        low=("low", "min"), close=("close", "last"), volume=("volume", "sum"),
    ).reset_index(drop=True)
    return out


def candle_end(ts, tf, exchange):
    """When a candle that starts at ts is complete. 4H / day candles end at the market close, not ts + tf."""
    end = ts + tf
    if tf >= pd.Timedelta(minutes=240):
        close = ts.normalize() + (pd.Timedelta(hours=23, minutes=30) if exchange == "MCX"
                                  else pd.Timedelta(hours=15, minutes=30))
        end = min(end, close)
    return end


def fetch_candles(smart, item, interval, now, cloud=False):
    def days(default):                      # cloud filter ON -> load enough history for the Ichimoku cloud
        return max(default, CLOUD_DAYS.get(interval, default)) if cloud else default

    if interval == "FOUR_HOUR":
        d = _candles(smart, item, "ONE_HOUR", now - pd.Timedelta(days=days(45)), now)
        if not d.empty:
            d = _resample_4h(d, item["exchange"])
    elif interval == "ONE_DAY":
        d = _candles(smart, item, "ONE_DAY", now - pd.Timedelta(days=days(90)), now)
    else:
        d = _candles(smart, item, interval, now - pd.Timedelta(days=days(5)), now)
    return d[["date", "open", "high", "low", "close"]] if not d.empty else d


def fetch_bars(smart, item, since, now):
    d = _candles(smart, item, "ONE_MINUTE", since, now)
    return d.set_index("date")[["open", "high", "low", "close"]] if not d.empty else d


def fetch_ltp(smart, item):
    try:
        _gap("ltp", 0.2)
        res = smart.ltpData(item["exchange"], item["tradingsymbol"], str(item["token"]))
        return float(res["data"]["ltp"])
    except Exception:
        return None


LAST_API_ERROR = {"quote": "", "bulk": ""}


def _quote_from(d):
    ltp = float(d["ltp"])
    return {"ts": time.time(),
        "open": float(d.get("open", ltp)), "high": float(d.get("high", ltp)),
        "low": float(d.get("low", ltp)), "close": float(d.get("close", ltp)), "ltp": ltp,
    }


def fetch_quote(smart, item):
    try:
        _gap("ltp", 0.2)
        res = smart.ltpData(item["exchange"], item["tradingsymbol"], str(item["token"]))
        d = (res or {}).get("data")
        if not d:
            LAST_API_ERROR["quote"] = str((res or {}).get("message") or res)
            return None
        return _quote_from(d)
    except Exception as ex:
        LAST_API_ERROR["quote"] = f"{type(ex).__name__}: {ex}"
        return None


QUOTE_CHUNK = 50          # Angel getMarketData accepts max 50 tokens per request -> send big lists in chunks


def fetch_quotes_bulk(smart, items):
    """{token: quote}. Any number of stocks (sent in chunks of 50). Returns None only when NOTHING came back
       (failed / rate limited) - the caller must NOT hammer per-item calls."""
    if time.time() < QUOTE_BACKOFF[0]:
        LAST_API_ERROR["bulk"] = "rate limited - waiting"
        return None
    out = {}
    try:
        by_ex = {}
        for it in items:
            by_ex.setdefault(it["exchange"], []).append(str(it["token"]))
        reqs = [{ex: toks[i:i + QUOTE_CHUNK]} for ex, toks in by_ex.items() for i in range(0, len(toks), QUOTE_CHUNK)]
        for req in reqs:
            _gap("bulk", 1.2)
            res = smart.getMarketData("OHLC", req)
            fetched = ((res or {}).get("data") or {}).get("fetched") or []
            if not fetched:
                msg = str((res or {}).get("message") or res)[:200]
                LAST_API_ERROR["bulk"] = msg
                if _is_rate_err(msg):
                    QUOTE_BACKOFF[0] = time.time() + 4
                    break                      # stop now, keep what we already got
                continue                       # other chunks may still work
            for r in fetched:
                try:
                    out[str(r["symbolToken"])] = _quote_from(r)
                except (KeyError, TypeError, ValueError):
                    continue
    except Exception as ex:
        msg = f"{type(ex).__name__}: {ex}"
        LAST_API_ERROR["bulk"] = msg
        if _is_rate_err(msg):
            QUOTE_BACKOFF[0] = time.time() + 4
    return out or None


# ============================== INSTRUMENTS ==============================
NIFTY50_FALLBACK = (
    "ADANIENT ADANIPORTS APOLLOHOSP ASIANPAINT AXISBANK BAJAJ-AUTO BAJFINANCE BAJAJFINSV BEL BHARTIARTL CIPLA "
    "COALINDIA DRREDDY EICHERMOT ETERNAL GRASIM HCLTECH HDFCBANK HDFCLIFE HEROMOTOCO HINDALCO HINDUNILVR ICICIBANK "
    "INDUSINDBK INFY ITC JIOFIN JSWSTEEL KOTAKBANK LT M&M MARUTI NESTLEIND NTPC ONGC POWERGRID RELIANCE SBILIFE "
    "SBIN SHRIRAMFIN SUNPHARMA TATACONSUM TATAMOTORS TATASTEEL TCS TECHM TITAN TRENT ULTRACEMCO WIPRO"
).split()


@st.cache_data(ttl=86400, show_spinner=False)
def nifty50():
    try:
        r = requests.get(
            "https://niftyindices.com/IndexConstituent/ind_nifty50list.csv",
            headers={"User-Agent": "Mozilla/5.0"}, timeout=15,
        )
        r.raise_for_status()
        syms = pd.read_csv(io.StringIO(r.text))["Symbol"].str.strip().tolist()
        if len(syms) >= 40:
            return syms
    except Exception:
        pass
    return list(NIFTY50_FALLBACK)


MASTER_CACHE = "scrip_master_cache.pkl"


@st.cache_resource(ttl=86400, show_spinner=False)
def load_master():
    if os.path.exists(MASTER_CACHE) and pd.Timestamp(os.path.getmtime(MASTER_CACHE), unit="s").date() == pd.Timestamp.now().date():
        try:
            cached = pd.read_pickle(MASTER_CACHE)
            if "tick_size" in cached.columns:
                return cached
        except Exception:
            pass
    df = pd.DataFrame(requests.get(MASTER_URL, timeout=120).json())
    df.columns = [c.strip().lower() for c in df.columns]
    keep = [c for c in ("exch_seg", "symbol", "name", "token", "lotsize", "instrumenttype", "expiry", "tick_size") if c in df.columns]
    df = df[keep]
    try:
        df.to_pickle(MASTER_CACHE)
    except Exception:
        pass
    return df


def search_item(smart, exchange, text):
    cache = st.session_state.setdefault("search_cache", {})
    key = f"{exchange}:{text}"
    if key not in cache:
        cache[key] = None
        try:
            rows = (smart.searchScrip(exchange, text) or {}).get("data") or []
            rows = [r for r in rows if r["tradingsymbol"].upper() in (text, text + "-EQ")] or rows
            if rows:
                r = rows[0]
                cache[key] = {
                    "symbol": r["tradingsymbol"].replace("-EQ", ""),
                    "tradingsymbol": r["tradingsymbol"],
                    "token": r["symboltoken"], "exchange": exchange, "lot": 1,
                }
        except Exception:
            pass
    return cache[key]


SENSEX30 = set(
    "ADANIPORTS ASIANPAINT AXISBANK BAJFINANCE BAJAJFINSV BHARTIARTL ETERNAL HCLTECH HDFCBANK HINDUNILVR ICICIBANK "
    "INFY ITC KOTAKBANK LT M&M MARUTI NESTLEIND NTPC POWERGRID RELIANCE SBIN SUNPHARMA TATAMOTORS TATASTEEL TCS "
    "TECHM TITAN TRENT ULTRACEMCO".split()
)
MCX_MAIN = set("GOLD GOLDM GOLDPETAL SILVER SILVERM CRUDEOIL CRUDEOILM NATURALGAS COPPER ZINC ALUMINIUM LEAD NICKEL".split())
NFO_INDEX = {"NIFTY", "BANKNIFTY", "FINNIFTY", "MIDCPNIFTY"}


NSE_INDEX_FILES = {          # niftyindices.com constituent CSVs
    "Nifty 50": "ind_nifty50list", "Nifty Next 50": "ind_niftynext50list", "Nifty 100": "ind_nifty100list",
    "Nifty Bank": "ind_niftybanklist", "Nifty IT": "ind_niftyitlist", "Nifty Midcap 100": "ind_niftymidcap100list",
    "Nifty Auto": "ind_niftyautolist", "Nifty Pharma": "ind_niftypharmalist", "Nifty FMCG": "ind_niftyfmcglist",
    "Nifty Metal": "ind_niftymetallist", "Nifty Financial Services": "ind_niftyfinancelist",
}
MCX_GROUPS = {
    "Bullion": {"GOLD", "GOLDM", "SILVER", "SILVERM"},
    "Energy": {"CRUDEOIL", "CRUDEOILM", "NATURALGAS"},
    "Base Metals": {"COPPER", "ZINC", "ALUMINIUM", "LEAD", "NICKEL"},
}


def index_options(exchange):
    """Names for the 'Index' box under Exchange."""
    if exchange == "NSE":
        return list(NSE_INDEX_FILES)
    if exchange == "BSE":
        return ["Sensex 30"]
    if exchange == "NFO":
        return ["Index futures", "Nifty 50 stock futures"]
    return list(MCX_GROUPS)


@st.cache_data(ttl=86400, show_spinner=False)
def nse_index_members(index):
    """Symbols of one NSE index ([] when the download fails)."""
    if index == "Nifty 50":
        return nifty50()
    f = NSE_INDEX_FILES.get(index)
    if not f:
        return []
    try:
        r = requests.get(f"https://niftyindices.com/IndexConstituent/{f}.csv",
                         headers={"User-Agent": "Mozilla/5.0"}, timeout=15)
        r.raise_for_status()
        return [x.strip() for x in pd.read_csv(io.StringIO(r.text))["Symbol"].astype(str) if x.strip()]
    except Exception:
        return []


def index_members(exchange, index):
    """Upper-case names of the chosen indices (tuple of names; None / empty -> the exchange's default list)."""
    if not index:
        if exchange == "NFO":
            return NFO_INDEX | set(nifty50())
        if exchange == "MCX":
            return MCX_MAIN
        return set(SENSEX30) if exchange == "BSE" else {x.upper() for x in nifty50()}
    out = set()
    for ix in index:
        if exchange == "NSE":
            out |= {x.upper() for x in nse_index_members(ix)}
        elif exchange == "BSE":
            out |= set(SENSEX30)
        elif exchange == "NFO":
            out |= NFO_INDEX if ix == "Index futures" else set(nifty50())
        else:
            out |= set(MCX_GROUPS.get(ix, MCX_MAIN))
    return out


def exchange_list(df, exchange, index=None):
    index = tuple(index) if index else None
    d = df[df["exch_seg"] == exchange].copy()
    nm = d["name"].fillna("").str.upper()
    sy = d["symbol"].fillna("").str.upper()
    base = index_members(exchange, index)
    if exchange == "NSE":
        d = d[sy.str.endswith("-EQ") & nm.isin(base)]
        d["label"] = d["name"]
    elif exchange == "BSE":
        d = d[nm.isin(SENSEX30) | sy.isin(SENSEX30)]
        d["label"] = d["name"].where(nm.isin(SENSEX30), d["symbol"])
    else:
        itype = d["instrumenttype"].fillna("") if "instrumenttype" in d else pd.Series("", index=d.index)
        if exchange == "NFO" and not index:
            base = NFO_INDEX | set(nifty50())
        d = d[itype.str.startswith("FUT") & nm.isin(base)]
        d["exp"] = pd.to_datetime(d["expiry"], format="%d%b%Y", errors="coerce")
        d = d[d["exp"] >= pd.Timestamp.now().normalize()].sort_values("exp")
        d = d.drop_duplicates("name")
        d["label"] = d["symbol"]
    return d.drop_duplicates("label").sort_values("label")


@st.cache_data(ttl=3600, show_spinner=False)
def exchange_list_cached(exchange, index=None):
    return exchange_list(load_master(), exchange, tuple(index) if index else None)


def no_dim():
    st.markdown(
        """<style>
        [data-stale="true"], .stale-element, [data-testid="stElementContainer"][data-stale="true"],
        [data-testid="stSidebar"] [data-stale="true"] { opacity: 1 !important; transition: none !important; }
        </style>""",
        unsafe_allow_html=True,
    )


def to_item(row, exchange):
    try:
        lot = max(int(float(row.get("lotsize") or 1)), 1) if exchange in ("NFO", "MCX") else 1
    except ValueError:
        lot = 1
    try:
        tick = float(row.get("tick_size") or 5) / 100.0          # master gives tick in paise
        tick = tick if tick > 0 else 0.05
    except (TypeError, ValueError):
        tick = 0.05
    return {
        "symbol": row["label"], "tradingsymbol": row["symbol"], "token": row["token"],
        "exchange": exchange, "lot": lot, "tick": tick,
    }



def margin_factor(exchange):
    return FUTURES_MARGIN_PCT / 100 if exchange in ("NFO", "MCX") else 1.0



def _csv_button(label, df, name, key):
    empty = df is None or df.empty
    st.download_button(
        label, b"" if empty else df.to_csv(index=False).encode(),
        f"{name}_{now_ist():%Y%m%d}.csv", "text/csv", key=key, disabled=empty,
    )



def _ui_css():
    """ONE style block per form: popover pickers look like the dropdowns, labels / sections line up."""
    st.markdown(
        "<style>"
        "div[data-testid='stElementContainer']:has(> div[data-testid='stMarkdown'] style){display:none}"
        "div[data-testid='stPopover'] button{display:flex;justify-content:space-between;align-items:center;"
        "width:100%;min-height:auto;text-align:left;border-radius:.5rem;border:1px solid transparent;"
        "background:rgba(128,128,128,.16);background:color-mix(in srgb,currentColor 10%,transparent);"
        "color:inherit;font-weight:400;transition:border-color .15s}"
        "div[data-testid='stPopover'] button:hover{border-color:var(--primary-color,#ff4b4b)}"
        "div[data-testid='stPopover'] button > div{flex:1;text-align:left}"
        "div[data-testid='stPopover'] button p{text-align:left;margin:0}"
        "div[data-testid='stPopoverBody']{border-radius:.75rem;box-shadow:0 10px 28px rgba(0,0,0,.30);"
        "min-width:min(34rem,90vw)}"
        "div[data-testid='stPopoverBody'] div[data-testid='stHorizontalBlock']{flex-wrap:nowrap !important;gap:.5rem}"
        "div[data-testid='stPopoverBody'] div[data-testid='stColumn'],"
        "div[data-testid='stPopoverBody'] div[data-testid='column']{min-width:0 !important}"
        ".fld-l{font-size:.875rem;line-height:1.4;margin:0 0 .3rem 0;opacity:.92}"
        ".sec-h{display:flex;align-items:center;gap:.55rem;font-weight:600;font-size:1.05rem;margin:0 0 .6rem 0}"
        ".sec-h i{display:inline-block;width:.32rem;height:1.15rem;border-radius:3px;background:var(--primary-color,#ff4b4b)}"
        ".sec-h small{font-weight:400;opacity:.6;font-size:.8rem}"
        "div[data-testid='stVerticalBlockBorderWrapper']{border-radius:.9rem}"
        "</style>",
        unsafe_allow_html=True,
    )


def _lbl(text, help=None):
    """Field label drawn the same way for every control (so rows line up)."""
    tip = f" title=\"{help}\"" if help else ""
    st.markdown(f"<div class='fld-l'{tip}>{text}{' &#9432;' if help else ''}</div>", unsafe_allow_html=True)


def _section(title, sub=""):
    st.markdown(f"<div class='sec-h'><i></i>{title}" + (f" <small>{sub}</small>" if sub else "") + "</div>",
                unsafe_allow_html=True)


def _stock_picker(label, labels, key, default=None, button_label="Select stocks"):
    """Stock picker: dropdown-style button -> tick-box list; small 'Select all' / 'Clear' on its right side."""
    big = len(labels) > 300                      # huge lists (NFO etc.) keep the normal multiselect
    ck = {lb: f"{key}__ck_{lb}" for lb in labels}
    if big:
        all_key = f"{key}__all"
        if key not in st.session_state:
            st.session_state[key] = [x for x in (default or []) if x in labels]
    else:
        dset = set(default or [])
        for lb, k_ in ck.items():
            if k_ not in st.session_state:
                st.session_state[k_] = lb in dset

    def _sel_all():
        if big:
            st.session_state[all_key] = True
        else:
            for k_ in ck.values():
                st.session_state[k_] = True

    def _clear():
        if big:
            st.session_state[all_key] = False
            st.session_state[key] = []
        else:
            for k_ in ck.values():
                st.session_state[k_] = False

    if big:
        _lbl(label)
        n_big = len(labels) if st.session_state.get(all_key) else len(st.session_state.get(key, []))
        with st.popover(f"{button_label} · {n_big} selected" if n_big else button_label, use_container_width=True):
            lst, side = st.columns([6, 1.4])
            with lst:
                if st.session_state.get(all_key):
                    st.success(f"✅ All {len(labels)} selected")
                else:
                    st.multiselect(label, labels, key=key, label_visibility="collapsed")
            with side:
                st.button("Select all", key=f"{key}__btn_all", on_click=_sel_all, type="tertiary", use_container_width=True)
                st.button("Clear", key=f"{key}__btn_clr", on_click=_clear, type="tertiary", use_container_width=True)
        return list(labels) if st.session_state.get(all_key) else list(st.session_state.get(key, []))
    _lbl(label)
    n_sel = sum(1 for k_ in ck.values() if st.session_state.get(k_))
    with st.popover(f"{button_label} · {n_sel} selected" if n_sel else button_label, use_container_width=True):
        lst, side = st.columns([6, 1.4])
        with lst:
            with st.container(height=min(320, 38 * len(labels) + 12)):
                for lb in labels:
                    st.checkbox(lb, key=ck[lb])
        with side:
            st.button("Select all", key=f"{key}__btn_all", on_click=_sel_all, type="tertiary", use_container_width=True)
            st.button("Clear", key=f"{key}__btn_clr", on_click=_clear, type="tertiary", use_container_width=True)
    return [lb for lb in labels if st.session_state.get(ck[lb])]


SIZE_LABELS = {"amount": "Amount", "qty": "Qty", "equal": "Equal weight"}


def _equal_amt(capital, max_open, no_limit, n_items):
    """Equal weight = capital / max positions (or / number of selected stocks when there is no limit)."""
    n = n_items if no_limit else max_open
    return round(float(capital) / n, 2) if capital and n else None


def _sizing_inputs(c_mode, c_val, capital, max_open, no_limit, n_items, key,
                   cur_mode="amount", default_amt=None, cur_qty=None):
    """Dropdown (Amount / Qty / Equal weight) + the value box for the chosen option.
       Returns (size_mode, amount, qty). amount = Rs per position (equal weight: auto-calculated)."""
    keys = list(SIZE_LABELS)
    pick = c_mode.selectbox("Position", [SIZE_LABELS[k] for k in keys],
                            index=keys.index(cur_mode) if cur_mode in keys else 0, key=f"{key}_size_mode",
                            help="Amount = oru position-ku evvalavu Rs | Qty = oru position-ku evvalavu qty "
                                 "(shares; NFO/MCX-la lots) | Equal weight = capital / max positions "
                                 "(no limit na capital / select panna stocks)")
    mode = keys[[SIZE_LABELS[k] for k in keys].index(pick)]
    eq = _equal_amt(capital, max_open, no_limit, n_items)
    if mode == "qty":
        q = c_val.number_input("Qty", min_value=1, value=int(cur_qty) if cur_qty else None,
                               step=1, placeholder="Qty", key=f"{key}_size_qty")
        return mode, float(eq or 0), (int(q) if q else None)
    if mode == "equal":
        c_val.text_input("Capital / positions (auto)", value=f"{eq:,.2f}" if eq else "", disabled=True)
        return mode, eq, 0
    amt = c_val.number_input("Amount", min_value=1.0,
                             value=float(default_amt) if default_amt else None, step=1000.0, placeholder="Amount")
    return mode, amt, 0



# ============================== BACKTEST ==============================
# Same entry / exit / sizing rules as the paper engine, but run over HISTORY (From date -> To date).
#   Entry : a pattern completes on candle i  ->  buy at the OPEN of candle i+1 (paper buys at LTP right after the close)
#   Exit  : target % / optional SL % / time exit at square-off (max_hold days) - same as check_exits()
#   Sizing: Config.size_qty()  (amount / qty / equal weight), max open positions, free-cash cap - same as Engine._enter()
import bisect
from concurrent.futures import ThreadPoolExecutor, as_completed

# Angel One getCandleData max days per request (kept a little below the limit)
BT_CHUNK_DAYS = {"ONE_MINUTE": 28, "THREE_MINUTE": 58, "FIVE_MINUTE": 95, "TEN_MINUTE": 95,
                 "FIFTEEN_MINUTE": 190, "THIRTY_MINUTE": 190, "ONE_HOUR": 380, "ONE_DAY": 1900}
BT_CACHE_DIR = os.path.join(_DATA_DIR, "backtest_cache")
os.makedirs(BT_CACHE_DIR, exist_ok=True)
_BT_ORIGIN = pd.Timestamp("2015-01-01")          # fixed chunk grid -> past chunks are re-used from disk on every run


def _bt_load(smart, item, interval, start, end):
    """Candles from start to end for one stock (date, open, high, low, close), fetched in API-sized chunks.
       Chunks that lie completely in the past are cached on disk, so changing target % / patterns is instant."""
    base = "ONE_HOUR" if interval == "FOUR_HOUR" else interval
    step = pd.Timedelta(days=BT_CHUNK_DAYS[base])
    today = now_ist().normalize()
    cur = _BT_ORIGIN + ((pd.Timestamp(start) - _BT_ORIGIN) // step) * step
    parts = []
    while cur < end:
        nxt = cur + step
        fn = os.path.join(BT_CACHE_DIR, f"{item['exchange']}_{item['token']}_{base}_{cur:%Y%m%d}.pkl")
        full = nxt <= today                              # chunk is complete -> safe to cache
        d = None
        if full and os.path.exists(fn):
            try:
                d = pd.read_pickle(fn)
            except Exception:
                d = None
        if d is None:
            d = _candles(smart, item, base, cur, nxt - pd.Timedelta(minutes=1))
            if full and d is not None and not d.empty:
                try:
                    d.to_pickle(fn)
                except Exception:
                    pass
        if d is not None and not d.empty:
            parts.append(d)
        cur = nxt
    if not parts:
        return pd.DataFrame()
    d = pd.concat(parts).drop_duplicates("date").sort_values("date").reset_index(drop=True)
    d = d[(d["date"] >= start) & (d["date"] < end)].reset_index(drop=True)
    if interval == "FOUR_HOUR" and not d.empty:
        d = _resample_4h(d, item["exchange"])
    return d[["date", "open", "high", "low", "close"]] if not d.empty else d


def _bt_deadline(etime, ex, max_hold):
    """Square-off moment: exit_time() on the max_hold-th business day, counting the entry day as day 1."""
    day = np.busday_offset(np.datetime64(etime.date()), max(int(max_hold), 1) - 1, roll="forward")
    xt = exit_time(ex)
    return pd.Timestamp(day) + pd.Timedelta(hours=xt.hour, minutes=xt.minute)


def _bt_exit(T, O, H, L, C, i0, deadline, tgt, sl):
    """Walk forward from bar i0. SL is checked before target inside a bar (same as _check_exit).
       Returns (price, time, reason) or None when there is no bar to walk."""
    n, k, last = len(T), i0, None
    while k < n and T[k] < deadline:
        if sl:
            if O[k] <= sl:
                return float(O[k]), T[k], "SL (gap)"
            if L[k] <= sl:
                return float(sl), T[k], "SL"
        if O[k] >= tgt:
            return float(O[k]), T[k], "Target (gap)"
        if H[k] >= tgt:
            return float(tgt), T[k], "Target"
        last = k
        k += 1
    if last is None:
        return None
    if k < n:
        return float(C[last]), deadline, "Time exit"
    return float(C[last]), T[last], "Open at end of data"


def _bt_candidates(it, df, cfg, start, end, order):
    """Every pattern signal of one stock inside [start, end) -> (entry candidates, skipped-signal records)."""
    ex, sym = it["exchange"], it["symbol"]
    tf = pd.Timedelta(minutes=cfg.tf_min)
    sig = detect_patterns(df, cfg)
    pats = [p for p in cfg.patterns if p in sig.columns]
    if not pats or len(df) < 3:
        return [], []
    cloud_sel = cloud_list(cfg.cloud_filter)                # optional filter (off by default); the cloud column is ALWAYS filled
    cl = ichimoku_cloud(df)
    close = df["close"].astype(float)
    cpos = np.where(cl["top"].isna(), "n/a", np.where(close > cl["top"], "Above",
                    np.where(close < cl["bottom"], "Below", "Center")))
    T = df["date"].tolist()
    O = df["open"].astype(float).to_numpy()
    open_off = pd.Timedelta(hours=9) if ex == "MCX" else pd.Timedelta(hours=9, minutes=15)
    cands, skipped = [], []
    for i in np.flatnonzero(sig[pats].any(axis=1).to_numpy()):
        ts = T[i]
        if ts < start or ts >= end:
            continue
        rec = {"symbol": sym, "exchange": ex, "candle": ts,
               "pattern": "+".join(p for p in pats if bool(sig[p].iat[i])),
               "cloud": cpos[i]}
        if cloud_sel and cpos[i] not in cloud_sel:
            skipped.append({**rec, "status": f"SKIPPED (cloud {cpos[i]} - filter needs {' / '.join(cloud_sel)})"})
            continue
        cend = candle_end(ts, tf, ex)
        intraday = tf < pd.Timedelta(minutes=240)
        if intraday and cend.time() >= exit_time(ex):
            skipped.append({**rec, "status": f"SKIPPED (no new entries after {exit_time(ex):%H:%M} (square-off time))"})
            continue
        if i + 1 >= len(df):
            continue                                        # no next candle in the data yet
        j = i + 1
        if intraday and (T[j].date() != ts.date() or T[j] - cend > tf):
            skipped.append({**rec, "status": "SKIPPED (data gap after signal candle)"})
            continue
        etime = T[j] if tf < pd.Timedelta(minutes=1440) else T[j].normalize() + open_off
        cands.append({**rec, "etime": etime, "entry_raw": float(O[j]), "j": j, "item": it, "order": order})
    return cands, skipped


def _bt_portfolio(cands, cfg, exits_for):
    """Replays the entries in time order with ONE shared capital / max-position pool (like Engine._enter)."""
    cands = sorted(cands, key=lambda r: (r["etime"], r["order"]))
    open_, closed, skipped = [], [], []
    for c in cands:
        still = []
        for p in open_:                                    # positions that already exited free their slot + cash
            (closed if p["_xt"] <= c["etime"] else still).append(p)
        open_ = still
        rec = {k: c[k] for k in ("symbol", "exchange", "candle", "pattern", "cloud")}
        it, ex = c["item"], c["exchange"]
        if any(p["symbol"] == c["symbol"] and p["exchange"] == ex for p in open_):
            skipped.append({**rec, "status": "SKIPPED (already in position)"})
            continue
        if len(open_) >= cfg.max_open:
            skipped.append({**rec, "status": f"SKIPPED (positions full {len(open_)}/{cfg.max_open})"})
            continue
        entry = c["entry_raw"] * (1 + cfg.slippage_pct / 100)
        lot, mf = int(it.get("lot", 1)), margin_factor(ex)
        cash = (cfg.capital + sum(p["pnl"] for p in closed)
                - sum(p["entry"] * p["qty"] * p["_mf"] for p in open_))
        _, qty = cfg.size_qty(entry * lot * mf, lot, cash)
        if qty < 1:
            skipped.append({**rec, "status": f"SKIPPED (1 unit needs {entry * lot * mf:,.0f}; {cfg.size_text}, free cash {cash:,.0f})"})
            continue
        tgt = round(entry * (1 + cfg.target_pct / 100), 2)
        sl = round(entry * (1 - cfg.sl_pct / 100), 2) if cfg.sl_pct > 0 else None
        hit = exits_for(c, tgt, sl)
        if hit is None:
            skipped.append({**rec, "status": "SKIPPED (no price data after entry)"})
            continue
        raw_px, xt, reason, release = hit
        exit_px = raw_px * (1 - cfg.slippage_pct / 100)
        pnl = (exit_px - entry) * qty - cfg.brokerage_pct / 100 * (entry + exit_px) * qty
        open_.append({
            "symbol": c["symbol"], "exchange": ex, "pattern": c["pattern"], "cloud": c["cloud"],
            "signal_candle": c["candle"], "entry_time": c["etime"], "entry": round(entry, 2),
            "target": tgt, "stop_loss": sl, "qty": int(qty), "invested": round(entry * qty * mf, 2),
            "exit_time": xt, "exit": round(exit_px, 2), "reason": reason,
            "pnl": round(pnl, 2), "pnl_pct": round((exit_px / entry - 1) * 100, 2),
            "_xt": release, "_mf": mf,
        })
        skipped.append({**rec, "status": "ENTERED"})
    closed += open_
    return closed, skipped


def run_backtest(smart, cfg, items, exchange, d_from, d_to, precise=False, progress=None):
    """-> dict(trades, signals, errors). precise=True walks 1-minute candles for target / SL (slower, closer to live)."""
    tf = pd.Timedelta(minutes=cfg.tf_min)
    start, end = pd.Timestamp(d_from), pd.Timestamp(d_to) + pd.Timedelta(days=1)          # end = exclusive
    warm = pd.Timedelta(days=CLOUD_DAYS.get(cfg.interval, 10) + 5)      # always load enough history for the reference cloud column
    tail = pd.Timedelta(days=int(cfg.max_hold) * 2 + 5)                                    # room for exits after To date
    load_to = min(end + tail, now_ist() + pd.Timedelta(days=1))
    errors, cands, sigs, bars = [], [], [], {}

    def load(it):
        df = _bt_load(smart, it, cfg.interval, start - warm, load_to)
        b1 = _bt_load(smart, it, "ONE_MINUTE", start, load_to) if precise and not df.empty else None
        return it, df, b1

    done = 0
    with ThreadPoolExecutor(max_workers=8) as pool:
        futs = {pool.submit(load, it): n for n, it in enumerate(items)}
        for f in as_completed(futs):
            order = futs[f]
            done += 1
            if progress:
                progress(done, len(items), items[order]["symbol"])
            try:
                it, df, b1 = f.result()
            except Exception as ex_:
                errors.append(f"{items[order]['symbol']}: {ex_}")
                continue
            if df is None or df.empty:
                errors.append(f"{it['symbol']}: no candle data for this period")
                continue
            c, s = _bt_candidates(it, df, cfg, start, end, order)
            cands += c
            sigs += s
            src = b1 if (b1 is not None and not b1.empty) else df
            bars[(it["exchange"], it["symbol"])] = (
                src["date"].tolist(), src["open"].astype(float).to_numpy(), src["high"].astype(float).to_numpy(),
                src["low"].astype(float).to_numpy(), src["close"].astype(float).to_numpy(), src is df)
            if precise and (b1 is None or b1.empty):
                errors.append(f"{it['symbol']}: no 1-minute data, used {cfg.interval} candles for exits")

    def exits_for(c, tgt, sl):
        T, O, H, L, C, same_tf = bars[(c["exchange"], c["symbol"])]
        i0 = c["j"] if same_tf else bisect.bisect_left(T, c["etime"])
        deadline = _bt_deadline(c["etime"], c["exchange"], cfg.max_hold)
        hit = _bt_exit(T, O, H, L, C, i0, deadline, tgt, sl)
        if hit is None:
            return None
        px, xt, reason = hit
        # a target / SL hit happens INSIDE its candle -> the slot + cash are free only when that candle ends
        blen = tf if same_tf else pd.Timedelta(minutes=1)
        release = xt if reason == "Time exit" else min(xt + blen, deadline) if reason != "Open at end of data" else xt + blen
        return px, xt, reason, release

    closed, entered = _bt_portfolio(cands, cfg, exits_for)
    trades = pd.DataFrame(closed).drop(columns=["_xt", "_mf"], errors="ignore")
    if not trades.empty:
        trades = trades.sort_values(["exit_time", "entry_time"]).reset_index(drop=True)
    signals = pd.DataFrame(sigs + entered)
    if not signals.empty:
        signals = signals.sort_values(["candle", "symbol"]).reset_index(drop=True)
    return {"trades": trades, "signals": signals, "errors": errors}


def bt_stats(trades, capital):
    if trades is None or trades.empty:
        return {}
    pnl = trades["pnl"].astype(float)
    win = pnl > 0
    gp, gl = pnl[win].sum(), -pnl[~win].sum()
    eq = pnl.cumsum()
    dd = (np.maximum(eq.cummax(), 0) - eq).max()
    return {
        "net": float(pnl.sum()), "ret": float(pnl.sum() / capital * 100) if capital else 0.0,
        "n": int(len(pnl)), "wins": int(win.sum()), "losses": int((~win).sum()),
        "win_rate": float(win.mean() * 100), "pf": float(gp / gl) if gl > 0 else float("inf") if gp > 0 else 0.0,
        "avg": float(pnl.mean()), "best": float(pnl.max()), "worst": float(pnl.min()),
        "avg_win": float(pnl[win].mean()) if win.any() else 0.0,
        "avg_loss": float(pnl[~win].mean()) if (~win).any() else 0.0,
        "dd": float(dd), "dd_pct": float(dd / capital * 100) if capital else 0.0,
    }


def _bt_group(trades, col):
    t = trades.copy()
    if col == "pattern":
        t["pattern"] = t["pattern"].str.split("+")
        t = t.explode("pattern")
    g = t.groupby(col)["pnl"].agg(trades="count", net_pnl="sum", avg_pnl="mean",
                                  win_rate=lambda s: (s > 0).mean() * 100).round(2)
    return g.sort_values("net_pnl", ascending=False).reset_index()


def _bt_show(res, capital):
    trades, signals = res["trades"], res["signals"]
    for e in res["errors"][:15]:
        st.warning(e)
    if len(res["errors"]) > 15:
        st.caption(f"... and {len(res['errors']) - 15} more data warnings")
    if trades.empty:
        st.info("No trades in this period (no signal passed the filters). Try a longer period / more patterns / more stocks.")
        if signals is not None and not signals.empty:
            st.dataframe(signals, use_container_width=True, hide_index=True)
        return
    s = bt_stats(trades, capital)
    r1 = st.columns(4)
    r1[0].metric("Net P&L", f"{s['net']:,.0f}", f"{s['ret']:.2f}% of capital")
    r1[1].metric("Trades", s["n"], f"{s['wins']}W / {s['losses']}L", delta_color="off")
    r1[2].metric("Win rate", f"{s['win_rate']:.1f}%")
    r1[3].metric("Profit factor", "inf" if math.isinf(s["pf"]) else f"{s['pf']:.2f}")
    r2 = st.columns(4)
    r2[0].metric("Avg P&L / trade", f"{s['avg']:,.0f}")
    r2[1].metric("Avg win / avg loss", f"{s['avg_win']:,.0f} / {s['avg_loss']:,.0f}")
    r2[2].metric("Best / worst trade", f"{s['best']:,.0f} / {s['worst']:,.0f}")
    r2[3].metric("Max drawdown", f"{s['dd']:,.0f}", f"-{s['dd_pct']:.2f}% of capital", delta_color="off")

    eq = trades.set_index("exit_time")["pnl"].cumsum().rename("Cumulative P&L")
    st.line_chart(eq)

    t_tr, t_sg, t_st, t_pt, t_dy = st.tabs(["Trades", "Signals", "By stock", "By pattern", "By day"])
    with t_tr:
        st.dataframe(trades, use_container_width=True, hide_index=True)
        _csv_button("⬇ Trades CSV", trades, "backtest_trades", "bt_dl_trades")
    with t_sg:
        if signals is not None and not signals.empty:
            st.caption(signals["status"].str.replace(r"\s*\(.*", "", regex=True).value_counts().to_dict())
            st.dataframe(signals, use_container_width=True, hide_index=True)
            _csv_button("⬇ Signals CSV", signals, "backtest_signals", "bt_dl_signals")
    with t_st:
        st.dataframe(_bt_group(trades, "symbol"), use_container_width=True, hide_index=True)
    with t_pt:
        st.dataframe(_bt_group(trades, "pattern"), use_container_width=True, hide_index=True)
    with t_dy:
        d = trades.assign(day=pd.to_datetime(trades["exit_time"]).dt.date)
        day = d.groupby("day")["pnl"].agg(trades="count", net_pnl="sum").round(2).reset_index()
        st.bar_chart(day.set_index("day")["net_pnl"])
        st.dataframe(day, use_container_width=True, hide_index=True)
    st.caption("Backtest = history replay with today's index members (survivorship bias), entry at next candle open, "
               "SL checked before target inside one candle. Live paper results can differ slightly.")


def backtest_page():
    """BACKTEST: same conditions as the Strategy Builder + From date / To date -> replay on historical candles."""
    no_dim()
    _ui_css()
    h1, h2 = st.columns([6, 1])
    h1.title("Backtest")
    if h2.button("Logout", key="bt_logout", use_container_width=True):
        for k_ in ("smart", "client_id", "creds"):
            st.session_state.pop(k_, None)
        st.session_state["no_autologin"] = True
        st.rerun()
    smart = st.session_state.get("smart")
    try:
        master = load_master()
    except Exception as ex:
        master = None
        st.warning(f"Stock list load aagala ({ex}).")

    today = now_ist().date()
    with st.container(border=True):
        e1, e2, e3 = st.columns(3)
        exchange = e1.selectbox("Exchange", ["NSE", "BSE", "NFO", "MCX"], key="bt_exchange")
        capital = e2.number_input("Capital", min_value=10000.0, value=None, step=10000.0, placeholder="Capital", key="bt_capital")
        tf_label = e3.selectbox("Candle timeframe", list(TIMEFRAMES), index=None, placeholder="Select timeframe", key="bt_tf")
        d1, d2, d3 = st.columns(3)
        d_from = d1.date_input("From date", value=today - pd.Timedelta(days=30), max_value=today, key="bt_from")
        d_to = d2.date_input("To date", value=today, max_value=today, key="bt_to")
        precise = d3.checkbox("Accurate exits (1-minute candles - slower)", key="bt_precise",
                              help="Off = target / SL checked on the chosen timeframe candles (fast). "
                                   "On = checked on 1-minute candles like the live engine (more API calls).")

        with st.container(border=True):
            _section("Entry condition", "index, stocks, candle patterns, position size")
            ix1, _a, _b = st.columns(3)
            with ix1:
                index_pick = _stock_picker("Index", index_options(exchange), f"bt_index_{exchange}", button_label="Select index")
            items = []
            if master is not None:
                inst = exchange_list_cached(exchange, index_pick)
                labels = inst["label"].tolist()
                by_label = inst.set_index("label")
                ix_name = " + ".join(index_pick) if len(index_pick) <= 2 else f"{len(index_pick)} indices"
                picked = _stock_picker(f"{ix_name or exchange} stocks ({len(labels)})", labels,
                                       f"bt_stocks_{exchange}_{'+'.join(index_pick) or 'all'}",
                                       default=labels if index_pick else None)
                typed = st.text_input("Or type names (comma separated)", key="bt_typed")
                names, miss = list(picked), []
                for t in [x.strip().upper() for x in typed.split(",") if x.strip()]:
                    hit = inst[(inst["label"].str.upper() == t) | (inst["symbol"].str.upper() == t)
                               | (inst["name"].str.upper() == t)]
                    if hit.empty:
                        miss.append(t)
                    elif hit.iloc[0]["label"] not in names:
                        names.append(hit.iloc[0]["label"])
                if miss:
                    st.warning("Not found in " + exchange + ": " + ", ".join(miss))
                items = [to_item({**by_label.loc[n].to_dict(), "label": n}, exchange) for n in names]
                st.caption(f"✅ Total {len(items)} stocks selected (of {len(labels)} in the chosen index list)")
            picked_pats = _stock_picker(f"Candle patterns ({len(PATTERNS)})", list(PATTERNS), "bt_patterns",
                                        default=list(PATTERNS), button_label="Select candle patterns")
            cl1, _c2, _c3 = st.columns(3)
            with cl1:
                cloud_sel = _stock_picker("Ichimoku cloud (optional)", [CLOUD_LABEL[k] for k in CLOUD_OPTIONS],
                                          "bt_cloud", button_label="Select cloud position (optional)")
            cloud_pick = cloud_text([CLOUD_BY_LABEL[x] for x in cloud_sel])

            NO_LIMIT = "Select max (no limit)"
            m1, m2, m3 = st.columns(3)
            max_pick = m1.selectbox("Max open positions", [NO_LIMIT] + list(range(1, 26)) + [30, 40, 50], index=0, key="bt_max")
            no_limit = max_pick == NO_LIMIT
            max_open = 10 ** 6 if no_limit else int(max_pick)
            size_mode, position_amount, position_qty = _sizing_inputs(
                m2, m3, capital, max_open, no_limit, len(items), "bt",
                default_amt=None if (no_limit or not capital) else round(capital / max_open, 2))

        with st.container(border=True):
            _section("Exit condition", "target, optional stop loss / holding days")
            x1, x2, x3 = st.columns(3)
            target_pct = x1.number_input("Target (%)", min_value=0.01, value=None, step=0.01, format="%.2f",
                                         placeholder="Target %", key="bt_target")
            sl_pct = x2.number_input("Stop loss (%) - optional", min_value=0.0, value=0.0, step=0.1, format="%.2f", key="bt_sl")
            max_hold = x3.number_input("Max hold (days)", min_value=1, value=MAX_HOLD_DAYS, step=1, key="bt_hold",
                                       help="1 = same-day square-off at 15:15 (NSE) / 23:15 (MCX), like the paper engine.")
        run = st.button("▶ Run backtest", type="primary", key="bt_run")

    if run:
        missing = [n for n, v in (("Capital", capital), ("Candle timeframe", tf_label),
                                  (SIZE_LABELS[size_mode], position_qty if size_mode == "qty" else position_amount),
                                  ("Target %", target_pct)) if not v]
        if missing:
            st.error("Fill: " + ", ".join(missing))
        elif d_from > d_to:
            st.error("From date must be on or before To date.")
        elif not items:
            st.error("Stocks select pannunga.")
        elif not picked_pats:
            st.error("Candle patterns select pannunga.")
        elif smart is None:
            st.error("Angel One login illa (historical data-ku login venum).")
        else:
            interval, tf_min = TIMEFRAMES[tf_label]
            data = {"exchange": exchange, "items": items, "capital": float(capital), "interval": interval, "tf_min": tf_min,
                    "max_open": int(max_open), "no_limit": no_limit, "position_amount": float(position_amount or 0),
                    "size_mode": size_mode, "position_qty": int(position_qty or 0), "target_pct": float(target_pct),
                    "sl_pct": float(sl_pct or 0), "max_hold": int(max_hold), "patterns": list(picked_pats),
                    "cloud_filter": cloud_pick}
            cfg = _cfg_from_data(data)
            cfg.slippage_pct, cfg.brokerage_pct = 0.0, 0.0          # costs removed from the UI
            bar = st.progress(0.0, text="Loading history...")

            def _prog(n, total, sym):
                bar.progress(n / total, text=f"Loading history {n}/{total}  ({sym})")

            res = run_backtest(smart, cfg, items, exchange, d_from, d_to, precise, _prog)
            bar.empty()
            res["capital"] = float(capital)
            res["label"] = (f"{exchange} | {tf_label} | {d_from:%d %b %Y} → {d_to:%d %b %Y} | "
                            f"{len(items)} stocks | target {target_pct}%")
            st.session_state["bt_result"] = res

    res = st.session_state.get("bt_result")
    if res:
        st.subheader("Result")
        st.caption(res["label"])
        _bt_show(res, res["capital"])



# ============================== LOGIN (Angel One - needed only to download history) ==============================
def env_creds():
    c = tuple(os.getenv(k, "").strip() for k in ("ANGEL_API_KEY", "ANGEL_CLIENT_ID", "ANGEL_MPIN", "ANGEL_TOTP_SECRET"))
    if all(c):
        return c
    try:
        a = st.secrets["angel"]
        c = tuple(str(a.get(k, "")).strip() for k in ("api_key", "client_id", "mpin", "totp_secret"))
        if all(c):
            return c
    except Exception:
        pass
    return None


def login_page():
    no_dim()
    st.title("Angel One login")
    st.caption("Login is used only to download historical candles. No orders are placed.")
    ss = st.session_state
    with st.form("angel_login"):
        api_key = st.text_input("API key", type="password")
        client_id = st.text_input("Client ID")
        mpin = st.text_input("MPIN", type="password")
        totp = st.text_input("TOTP secret", type="password")
        go = st.form_submit_button("Connect", type="primary")
    if go:
        if not all(x.strip() for x in (api_key, client_id, mpin, totp)):
            st.error("Fill all 4 fields.")
            return
        with st.spinner("Angel One login..."):
            sm, err = angel_login(api_key, client_id, mpin, totp)
        if sm is None:
            st.error(err)
            return
        ss.smart, ss.client_id, ss.creds = sm, client_id.strip().upper(), (api_key, client_id, mpin, totp)
        ss.pop("no_autologin", None)
        st.rerun()


# ============================== ENTRY ==============================
st.set_page_config(page_title="Backtest", layout="wide", initial_sidebar_state="collapsed")
_ss = st.session_state
if "smart" not in _ss and not _ss.get("no_autologin"):
    _creds = env_creds()                                  # optional: ANGEL_* env / secrets -> auto login
    if _creds:
        with st.spinner("Angel One login..."):
            _sm, _err = angel_login(*_creds)
        if _sm is not None:
            _ss.smart, _ss.client_id, _ss.creds = _sm, _creds[1].strip().upper(), _creds
        else:
            st.warning(f"Auto login failed: {_err}")

if "smart" not in _ss:
    login_page()
else:
    # re-login every 8 hours (Angel session expiry)
    if _ss.get("creds") and time.time() - _ss.setdefault("login_time", time.time()) > 8 * 3600:
        _sm, _err = angel_login(*_ss.creds)
        if _sm is not None:
            _ss.smart, _ss.login_time = _sm, time.time()
    backtest_page()
