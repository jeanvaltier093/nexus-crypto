'use strict';

require('dotenv').config();
const express = require('express');
const axios   = require('axios');
const cron    = require('node-cron');
const cors    = require('cors');
const path    = require('path');

// ================================================================
// CONFIG & VALIDATION
// ================================================================
const PORT        = process.env.PORT || 3000;
const TWELVE_KEY  = process.env.TWELVE_DATA_KEY;
const JSONBIN_KEY = process.env.JSONBIN_KEY;
const BIN_ID      = process.env.JSONBIN_BIN_ID || '69f768d7856a6821899fed2a';

if (!TWELVE_KEY)  { console.error('❌ MISSING ENV: TWELVE_DATA_KEY');  process.exit(1); }
if (!JSONBIN_KEY) { console.error('❌ MISSING ENV: JSONBIN_KEY');       process.exit(1); }

// ================================================================
// CONSTANTS
// ================================================================
const CRYPTOS  = ['BTC/USD', 'ETH/USD', 'SOL/USD', 'BNB/USD', 'XRP/USD'];
const CANDLES  = 250;   // candles fetched per symbol
const SL_PCT   = 0.03;  // 3% stop-loss
const TP_PCT   = 0.05;  // 5% take-profit

// Production combos from backtest (Rang 4 BUY / Rang 22 SELL)
const BUY_COMBO  = ['macdCrossUp', 'ema50_200Bear', 'aroonBear', 'atrHigh', 'momentumAccelBear'];
const SELL_COMBO = ['mfiOversold', 'accDistBear', 'atrNormal', 'cciOverbought', 'higherHighs'];

const BACKTEST = {
  BUY:  { wr: 63, wfMin: 54, wfMoy: 69, pf: 2.78 },
  SELL: { wr: 62, wfMin: 38, wfMoy: 69, pf: 2.72 }
};

// ================================================================
// UTILS
// ================================================================
const sleep = ms => new Promise(r => setTimeout(r, ms));
const uid   = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 8);

// ================================================================
// INDICATOR ENGINE
// ================================================================

/**
 * EMA — Exponential Moving Average
 * result[k] aligns with data[period-1+k]
 * Returns array of length (data.length - period + 1), or null
 */
function calcEMA(data, period) {
  if (!data || data.length < period) return null;
  const k = 2 / (period + 1);
  let val = data.slice(0, period).reduce((a, b) => a + b, 0) / period;
  const out = [val];
  for (let i = period; i < data.length; i++) {
    val = data[i] * k + val * (1 - k);
    out.push(val);
  }
  return out; // length = data.length - period + 1
}

/**
 * ATR(14) — Wilder's Average True Range
 * result[k] aligns with candle[14+k]
 * Returns array of length (n - 14), or null
 */
function calcATR(H, L, C, period) {
  const n = C.length;
  if (n < period + 1) return null;
  const trs = [];
  for (let i = 1; i < n; i++) {
    trs.push(Math.max(
      H[i] - L[i],
      Math.abs(H[i] - C[i - 1]),
      Math.abs(L[i] - C[i - 1])
    ));
  }
  let val = trs.slice(0, period).reduce((a, b) => a + b, 0) / period;
  const out = [val];
  for (let i = period; i < trs.length; i++) {
    val = (val * (period - 1) + trs[i]) / period;
    out.push(val);
  }
  return out; // length = n - period
}

/**
 * MACD(12, 26, 9)
 * line[k]  aligns with candle[25+k]  (length = n-25)
 * sig[j]   aligns with line[8+j]     (length = n-33)
 * → for crossover: sig[i] pairs with line[8+i]
 * Returns { line, sig } or null
 */
function calcMACD(C) {
  const e12 = calcEMA(C, 12); // e12[k] → C[11+k]
  const e26 = calcEMA(C, 26); // e26[k] → C[25+k]
  if (!e12 || !e26) return null;

  // line[k] = e12[k+14] - e26[k]  →  C[25+k]
  const line = [];
  for (let k = 0; k < e26.length; k++) {
    line.push(e12[k + 14] - e26[k]);
  }
  if (line.length < 9) return null;

  // sig[j] = EMA9(line)[j]  →  line[8+j]  →  C[33+j]
  const sig = calcEMA(line, 9);
  if (!sig || sig.length < 2) return null;

  return { line, sig };
}

/**
 * Aroon(25)
 * up[k], dn[k] align with candle[25+k]
 * Returns { up, dn } or null
 */
function calcAroon(H, L, period) {
  const n = H.length;
  if (n < period + 1) return null;
  const up = [], dn = [];
  for (let i = period; i < n; i++) {
    const slH = H.slice(i - period, i + 1);
    const slL = L.slice(i - period, i + 1);
    const hiIdx = slH.indexOf(Math.max(...slH));
    const loIdx = slL.indexOf(Math.min(...slL));
    up.push((hiIdx / period) * 100);
    dn.push((loIdx / period) * 100);
  }
  return { up, dn }; // each array length = n - period
}

/**
 * MFI(14) — Money Flow Index
 * result[k] aligns with candle[14+k]
 * Returns array or null (null if no volume data)
 */
function calcMFI(H, L, C, V, period) {
  const n = C.length;
  if (n < period + 1) return null;
  if (!V.some(v => v > 0)) return null; // no volume data

  const tp  = C.map((c, i) => (H[i] + L[i] + c) / 3);
  const rmf = tp.map((t, i) => t * V[i]);
  const out = [];

  for (let i = period; i < n; i++) {
    let pos = 0, neg = 0;
    for (let j = i - period + 1; j <= i; j++) {
      if (tp[j] > tp[j - 1])      pos += rmf[j];
      else if (tp[j] < tp[j - 1]) neg += rmf[j];
    }
    if (neg === 0) { out.push(pos === 0 ? 50 : 100); continue; }
    out.push(100 - 100 / (1 + pos / neg));
  }
  return out; // length = n - period
}

/**
 * CCI(20) — Commodity Channel Index
 * result[k] aligns with candle[19+k]
 * Returns array or null
 */
function calcCCI(H, L, C, period) {
  const n = C.length;
  if (n < period) return null;
  const tp  = C.map((c, i) => (H[i] + L[i] + c) / 3);
  const out = [];
  for (let i = period - 1; i < n; i++) {
    const sl   = tp.slice(i - period + 1, i + 1);
    const mean = sl.reduce((a, b) => a + b, 0) / period;
    const md   = sl.reduce((a, b) => a + Math.abs(b - mean), 0) / period;
    out.push(md === 0 ? 0 : (tp[i] - mean) / (0.015 * md));
  }
  return out; // length = n - period + 1
}

/**
 * Accumulation / Distribution line
 * Same length as input (cumulative)
 */
function calcAccDist(H, L, C, V) {
  const out = [];
  let ad = 0;
  for (let i = 0; i < C.length; i++) {
    const hl = H[i] - L[i];
    if (hl > 0) {
      const mfm = ((C[i] - L[i]) - (H[i] - C[i])) / hl;
      ad += mfm * V[i];
    }
    out.push(ad);
  }
  return out; // length = n
}

/**
 * Momentum(10) — Close[i] - Close[i-10]
 * result[k] aligns with candle[10+k]
 * Returns array or null
 */
function calcMomentum(C, period) {
  const n = C.length;
  if (n < period + 1) return null;
  return C.slice(period).map((c, i) => c - C[i]); // length = n - period
}

// ================================================================
// SIGNAL DETECTION
// ================================================================
function detectSignals(candles) {
  const n = candles.length;
  const C = candles.map(c => c.close);
  const H = candles.map(c => c.high);
  const L = candles.map(c => c.low);
  const V = candles.map(c => c.volume);

  // Compute all indicators
  const E50  = calcEMA(C, 50);
  const E200 = calcEMA(C, 200);
  const MACD = calcMACD(C);
  const ATR  = calcATR(H, L, C, 14);
  const AR   = calcAroon(H, L, 25);
  const MFI  = calcMFI(H, L, C, V, 14);
  const CCI  = calcCCI(H, L, C, 20);
  const AD   = calcAccDist(H, L, C, V);
  const MOM  = calcMomentum(C, 10);

  const s = {};

  // ── BUY SIGNAL 1: macdCrossUp ─────────────────────────────────
  // MACD line crosses above signal line (bullish crossover)
  // Verified: sig[i] pairs with line[8+i] for all i
  if (MACD && MACD.sig.length >= 2) {
    const { line, sig } = MACD;
    const i = sig.length - 1;
    s.macdCrossUp = line[8 + i] > sig[i] && line[8 + i - 1] <= sig[i - 1];
  } else {
    s.macdCrossUp = false;
  }

  // ── BUY SIGNAL 2: ema50_200Bear ───────────────────────────────
  // EMA50 below EMA200 = bearish trend context (death cross region)
  s.ema50_200Bear = !!(E50 && E200 &&
    E50[E50.length - 1] < E200[E200.length - 1]);

  // ── BUY SIGNAL 3: aroonBear ───────────────────────────────────
  // AroonDown > AroonUp = bearish momentum in Aroon
  s.aroonBear = !!(AR && AR.dn.length > 0 &&
    AR.dn[AR.dn.length - 1] > AR.up[AR.up.length - 1]);

  // ── BUY SIGNAL 4: atrHigh ─────────────────────────────────────
  // ATR > 1.5× its own 20-period mean = elevated volatility
  if (ATR && ATR.length >= 20) {
    const win  = ATR.slice(-20);
    const mean = win.reduce((a, b) => a + b, 0) / 20;
    s.atrHigh  = ATR[ATR.length - 1] > 1.5 * mean;
  } else {
    s.atrHigh = false;
  }

  // ── BUY SIGNAL 5: momentumAccelBear ──────────────────────────
  // Momentum declining for 3 consecutive bars
  if (MOM && MOM.length >= 3) {
    const l = MOM.length;
    s.momentumAccelBear = MOM[l - 1] < MOM[l - 2] && MOM[l - 2] < MOM[l - 3];
  } else {
    s.momentumAccelBear = false;
  }

  // ── SELL SIGNAL 1: mfiOversold ────────────────────────────────
  // MFI < 20 = money exiting despite price action (distribution)
  s.mfiOversold = !!(MFI && MFI.length > 0 && MFI[MFI.length - 1] < 20);

  // ── SELL SIGNAL 2: accDistBear ────────────────────────────────
  // A/D line falling = net distribution
  s.accDistBear = !!(AD && AD.length >= 2 &&
    AD[AD.length - 1] < AD[AD.length - 2]);

  // ── SELL SIGNAL 3: atrNormal ─────────────────────────────────
  // ATR in calm range (0.5× to 1.2× mean) = low-volatility sell setup
  if (ATR && ATR.length >= 20) {
    const win  = ATR.slice(-20);
    const mean = win.reduce((a, b) => a + b, 0) / 20;
    const last = ATR[ATR.length - 1];
    s.atrNormal = last >= 0.5 * mean && last <= 1.2 * mean;
  } else {
    s.atrNormal = false;
  }

  // ── SELL SIGNAL 4: cciOverbought ─────────────────────────────
  // CCI > 100 = overbought momentum
  s.cciOverbought = !!(CCI && CCI.length > 0 && CCI[CCI.length - 1] > 100);

  // ── SELL SIGNAL 5: higherHighs ───────────────────────────────
  // 3 consecutive higher highs = extension / exhaustion
  s.higherHighs = n >= 3 &&
    H[n - 1] > H[n - 2] && H[n - 2] > H[n - 3];

  // ── COMBO CHECK ───────────────────────────────────────────────
  const buyOk  = BUY_COMBO.every(k => s[k] === true);
  const sellOk = SELL_COMBO.every(k => s[k] === true);

  return { signals: s, buyOk, sellOk };
}

// ================================================================
// JSONBIN
// ================================================================
const BIN_URL = `https://api.jsonbin.io/v3/b/${BIN_ID}`;
const READ_HEADERS  = { 'X-Master-Key': JSONBIN_KEY };
const WRITE_HEADERS = { 'X-Master-Key': JSONBIN_KEY, 'Content-Type': 'application/json' };

async function readBin() {
  const r = await axios.get(`${BIN_URL}/latest`, {
    headers: READ_HEADERS, timeout: 12000
  });
  return r.data.record;
}

async function writeBin(data) {
  const r = await axios.put(BIN_URL, data, {
    headers: WRITE_HEADERS, timeout: 12000
  });
  return r.data.record;
}

// ================================================================
// TWELVE DATA FETCH
// ================================================================
async function fetchCandles(symbol) {
  let lastErr;
  for (let attempt = 1; attempt <= 3; attempt++) {
    try {
      const res = await axios.get('https://api.twelvedata.com/time_series', {
        params: {
          symbol,
          interval:   '1day',
          outputsize: CANDLES,
          apikey:     TWELVE_KEY,
          format:     'JSON'
        },
        timeout: 20000
      });

      if (res.data.status === 'error') {
        throw new Error(`Twelve Data: ${res.data.message}`);
      }

      const vals = res.data.values;
      if (!vals || vals.length < 50) {
        throw new Error(`Not enough candles for ${symbol}: ${vals?.length}`);
      }

      // Twelve Data returns newest-first — reverse to chronological
      return vals.reverse().map(v => ({
        datetime: v.datetime,
        open:   parseFloat(v.open),
        high:   parseFloat(v.high),
        low:    parseFloat(v.low),
        close:  parseFloat(v.close),
        volume: parseFloat(v.volume) || 0
      }));

    } catch (e) {
      lastErr = e;
      if (attempt < 3) {
        console.warn(`  ⚠️  Retry ${attempt}/3 for ${symbol}: ${e.message}`);
        await sleep(10000);
      }
    }
  }
  throw lastErr;
}

// ================================================================
// STATS RECALCULATION
// ================================================================
function recalcStats(trades) {
  const closed = trades.filter(t => t.result !== null);

  const st = {
    totalTrades: closed.length,
    wins: 0, losses: 0,
    winRate: null, profitFactor: null,
    totalPnlPct: 0, maxDrawdown: null,
    currentStreak: 0, currentStreakType: null,
    byDirection: {
      BUY:  { trades: 0, wins: 0, losses: 0, winRate: null },
      SELL: { trades: 0, wins: 0, losses: 0, winRate: null }
    },
    byCrypto: Object.fromEntries(
      CRYPTOS.map(c => [c, { trades: 0, wins: 0, losses: 0, winRate: null }])
    )
  };

  if (!closed.length) return st;

  let totalGain = 0, totalLoss = 0;
  let equity = 0, peak = 0, maxDD = 0;

  for (const t of closed) {
    const win = t.result === 'WIN';
    if (win) { st.wins++;   totalGain += Math.abs(t.pnlPct ?? TP_PCT * 100); }
    else     { st.losses++; totalLoss += Math.abs(t.pnlPct ?? SL_PCT * 100); }

    st.totalPnlPct += (t.pnlPct ?? 0);
    equity += (t.pnlPct ?? 0);
    if (equity > peak) peak = equity;
    const dd = peak - equity;
    if (dd > maxDD) maxDD = dd;

    // By direction
    if (st.byDirection[t.direction]) {
      st.byDirection[t.direction].trades++;
      if (win) st.byDirection[t.direction].wins++;
      else     st.byDirection[t.direction].losses++;
    }

    // By crypto
    if (st.byCrypto[t.crypto]) {
      st.byCrypto[t.crypto].trades++;
      if (win) st.byCrypto[t.crypto].wins++;
      else     st.byCrypto[t.crypto].losses++;
    }
  }

  st.winRate       = Math.round(st.wins / closed.length * 100);
  st.profitFactor  = totalLoss > 0 ? parseFloat((totalGain / totalLoss).toFixed(2)) : null;
  st.maxDrawdown   = parseFloat(maxDD.toFixed(2));
  st.totalPnlPct   = parseFloat(st.totalPnlPct.toFixed(2));

  for (const d of ['BUY', 'SELL']) {
    const x = st.byDirection[d];
    x.winRate = x.trades > 0 ? Math.round(x.wins / x.trades * 100) : null;
  }
  for (const c of CRYPTOS) {
    const x = st.byCrypto[c];
    x.winRate = x.trades > 0 ? Math.round(x.wins / x.trades * 100) : null;
  }

  // Current streak
  if (closed.length > 0) {
    const lastResult = closed[closed.length - 1].result;
    let streak = 0;
    for (let i = closed.length - 1; i >= 0 && closed[i].result === lastResult; i--) streak++;
    st.currentStreak     = streak;
    st.currentStreakType = lastResult;
  }

  return st;
}

// ================================================================
// MAIN SCAN
// ================================================================
let scanRunning = false;

async function runScan() {
  if (scanRunning) {
    console.log('⚠️  Scan already running — skipped');
    return { skipped: true };
  }
  scanRunning = true;
  const scanTime = new Date().toISOString();
  console.log(`\n📡 Scan started — ${scanTime}`);

  const newSignals = [];
  const errors     = [];

  for (const crypto of CRYPTOS) {
    try {
      console.log(`  → ${crypto}`);
      const candles = await fetchCandles(crypto);
      const { signals, buyOk, sellOk } = detectSignals(candles);
      const price = candles[candles.length - 1].close;

      if (buyOk) {
        newSignals.push({
          id:          uid(),
          crypto,
          direction:   'BUY',
          price,
          sl:          parseFloat((price * (1 - SL_PCT)).toFixed(8)),
          tp:          parseFloat((price * (1 + TP_PCT)).toFixed(8)),
          triggeredAt: scanTime,
          signals:     BUY_COMBO,
          details:     signals,
          status:      'pending'
        });
        console.log(`     ✅ BUY signal!`);
      }

      if (sellOk) {
        newSignals.push({
          id:          uid(),
          crypto,
          direction:   'SELL',
          price,
          sl:          parseFloat((price * (1 + SL_PCT)).toFixed(8)),
          tp:          parseFloat((price * (1 - TP_PCT)).toFixed(8)),
          triggeredAt: scanTime,
          signals:     SELL_COMBO,
          details:     signals,
          status:      'pending'
        });
        console.log(`     ✅ SELL signal!`);
      }

      if (!buyOk && !sellOk) console.log(`     ○  No signal`);

      await sleep(500); // buffer between API calls
    } catch (e) {
      console.error(`     ❌ ${crypto}: ${e.message}`);
      errors.push({ crypto, error: e.message });
    }
  }

  // Persist to JSONBin
  try {
    const data       = await readBin();
    data.lastScan    = scanTime;
    data.signals     = newSignals;
    await writeBin(data);
    console.log(`✅ Scan done — ${newSignals.length} signal(s), ${errors.length} error(s)\n`);
  } catch (e) {
    console.error(`❌ JSONBin write failed: ${e.message}`);
    errors.push({ crypto: 'JSONBin', error: e.message });
  }

  scanRunning = false;
  return { signals: newSignals, errors, scanTime };
}

// ================================================================
// EXPRESS APP
// ================================================================
const app = express();
app.use(cors());
app.use(express.json());
app.use(express.static(path.join(__dirname, 'public')));

// ── Health check ─────────────────────────────────────────────────
app.get('/health', (_, res) => {
  res.json({ ok: true, time: new Date().toISOString(), scanning: scanRunning });
});

// ── Manual scan ──────────────────────────────────────────────────
app.get('/api/scan', async (req, res) => {
  try {
    const result = await runScan();
    res.json({ success: true, ...result });
  } catch (e) {
    res.status(500).json({ success: false, error: e.message });
  }
});

// ── Last scan signals ─────────────────────────────────────────────
app.get('/api/signals', async (_, res) => {
  try {
    const data = await readBin();
    res.json({ lastScan: data.lastScan, signals: data.signals || [] });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

// ── All trades ───────────────────────────────────────────────────
app.get('/api/trades', async (_, res) => {
  try {
    const data = await readBin();
    res.json({ trades: data.trades || [] });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

// ── Open a trade ─────────────────────────────────────────────────
app.post('/api/trade', async (req, res) => {
  const { crypto, direction, entryPrice, sl, tp, signalId } = req.body;

  // Validation
  if (!crypto || !direction || entryPrice == null || sl == null || tp == null)
    return res.status(400).json({ error: 'Required fields: crypto, direction, entryPrice, sl, tp' });
  if (!['BUY', 'SELL'].includes(direction))
    return res.status(400).json({ error: 'direction must be BUY or SELL' });
  if (!CRYPTOS.includes(crypto))
    return res.status(400).json({ error: `crypto must be one of: ${CRYPTOS.join(', ')}` });
  if (isNaN(parseFloat(entryPrice)) || parseFloat(entryPrice) <= 0)
    return res.status(400).json({ error: 'entryPrice must be a positive number' });
  if (isNaN(parseFloat(sl)) || parseFloat(sl) <= 0)
    return res.status(400).json({ error: 'sl must be a positive number' });
  if (isNaN(parseFloat(tp)) || parseFloat(tp) <= 0)
    return res.status(400).json({ error: 'tp must be a positive number' });

  try {
    const data  = await readBin();
    const trade = {
      id:         uid(),
      signalId:   signalId || null,
      crypto,
      direction,
      entryPrice: parseFloat(entryPrice),
      sl:         parseFloat(sl),
      tp:         parseFloat(tp),
      entryDate:  new Date().toISOString(),
      exitDate:   null,
      exitPrice:  null,
      result:     null,
      pnlPct:     null
    };

    // Mark corresponding signal as taken
    const sig = (data.signals || []).find(s => s.id === signalId);
    if (sig) sig.status = 'taken';

    data.trades.push(trade);
    data.stats = recalcStats(data.trades);
    await writeBin(data);
    res.json({ success: true, trade });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

// ── Close a trade ─────────────────────────────────────────────────
app.put('/api/trade/:id', async (req, res) => {
  const { exitPrice, result } = req.body;

  // Validation
  if (exitPrice == null || !result)
    return res.status(400).json({ error: 'Required fields: exitPrice, result' });
  if (!['WIN', 'LOSS'].includes(result))
    return res.status(400).json({ error: 'result must be WIN or LOSS' });
  if (isNaN(parseFloat(exitPrice)) || parseFloat(exitPrice) <= 0)
    return res.status(400).json({ error: 'exitPrice must be a positive number' });

  try {
    const data  = await readBin();
    const trade = (data.trades || []).find(t => t.id === req.params.id);

    if (!trade) return res.status(404).json({ error: 'Trade not found' });
    if (trade.result !== null) return res.status(400).json({ error: 'Trade already closed' });

    trade.exitPrice = parseFloat(exitPrice);
    trade.exitDate  = new Date().toISOString();
    trade.result    = result;

    // PnL% = signed return relative to direction
    const ep = trade.entryPrice, xp = trade.exitPrice;
    trade.pnlPct = parseFloat((
      trade.direction === 'BUY'
        ? (xp - ep) / ep * 100
        : (ep - xp) / ep * 100
    ).toFixed(2));

    data.stats = recalcStats(data.trades);
    await writeBin(data);
    res.json({ success: true, trade });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

// ── Stats ────────────────────────────────────────────────────────
app.get('/api/stats', async (_, res) => {
  try {
    const data = await readBin();
    res.json(data.stats || {});
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

// ================================================================
// CRON — 08:00 Paris time every day
// ================================================================
cron.schedule('0 8 * * *', () => {
  console.log('⏰ Cron triggered — daily scan');
  runScan().catch(e => console.error('Cron scan error:', e.message));
}, { scheduled: true, timezone: 'Europe/Paris' });

// ================================================================
// START
// ================================================================
app.listen(PORT, () => {
  console.log(`\n🚀 NEXUS CRYPTO — Port ${PORT}`);
  console.log(`   Bin ID   : ${BIN_ID}`);
  console.log(`   Pairs    : ${CRYPTOS.join(' | ')}`);
  console.log(`   SL / TP  : ${SL_PCT * 100}% / ${TP_PCT * 100}%`);
  console.log(`   Cron     : 08:00 Europe/Paris\n`);
});
