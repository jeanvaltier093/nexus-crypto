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
const PORT         = process.env.PORT || 3000;
const TWELVE_KEY   = process.env.TWELVE_DATA_KEY;
const FIREBASE_URL = process.env.FIREBASE_URL;
 
if (!TWELVE_KEY)   { console.error('❌ MISSING ENV: TWELVE_DATA_KEY'); process.exit(1); }
if (!FIREBASE_URL) { console.error('❌ MISSING ENV: FIREBASE_URL');    process.exit(1); }
 
// ================================================================
// CONSTANTS
// ================================================================
const CRYPTOS  = ['BTC/USD', 'ETH/USD', 'SOL/USD', 'BNB/USD', 'XRP/USD'];
const CANDLES  = 1000;
const SL_PCT   = 0.03;
const TP_PCT   = 0.05;
 
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
function calcEMA(data, period) {
  if (!data || data.length < period) return null;
  const k = 2 / (period + 1);
  let val = data.slice(0, period).reduce((a, b) => a + b, 0) / period;
  const out = [val];
  for (let i = period; i < data.length; i++) {
    val = data[i] * k + val * (1 - k);
    out.push(val);
  }
  return out;
}
 
function calcATR(H, L, C, period) {
  const n = C.length;
  if (n < period + 1) return null;
  const trs = [];
  for (let i = 1; i < n; i++) {
    trs.push(Math.max(H[i]-L[i], Math.abs(H[i]-C[i-1]), Math.abs(L[i]-C[i-1])));
  }
  let val = trs.slice(0, period).reduce((a, b) => a + b, 0) / period;
  const out = [val];
  for (let i = period; i < trs.length; i++) {
    val = (val * (period - 1) + trs[i]) / period;
    out.push(val);
  }
  return out;
}
 
function calcMACD(C) {
  const e12 = calcEMA(C, 12);
  const e26 = calcEMA(C, 26);
  if (!e12 || !e26) return null;
  const line = [];
  for (let k = 0; k < e26.length; k++) line.push(e12[k + 14] - e26[k]);
  if (line.length < 9) return null;
  const sig = calcEMA(line, 9);
  if (!sig || sig.length < 2) return null;
  return { line, sig };
}
 
function calcAroon(H, L, period) {
  const n = H.length;
  if (n < period + 1) return null;
  const up = [], dn = [];
  for (let i = period; i < n; i++) {
    const slH = H.slice(i - period, i + 1);
    const slL = L.slice(i - period, i + 1);
    up.push((slH.indexOf(Math.max(...slH)) / period) * 100);
    dn.push((slL.indexOf(Math.min(...slL)) / period) * 100);
  }
  return { up, dn };
}
 
function calcMFI(H, L, C, V, period) {
  const n = C.length;
  if (n < period + 1) return null;
  if (!V.some(v => v > 0)) return null;
  const tp  = C.map((c, i) => (H[i] + L[i] + c) / 3);
  const rmf = tp.map((t, i) => t * V[i]);
  const out = [];
  for (let i = period; i < n; i++) {
    let pos = 0, neg = 0;
    for (let j = i - period + 1; j <= i; j++) {
      if (tp[j] > tp[j-1]) pos += rmf[j];
      else if (tp[j] < tp[j-1]) neg += rmf[j];
    }
    if (neg === 0) { out.push(pos === 0 ? 50 : 100); continue; }
    out.push(100 - 100 / (1 + pos / neg));
  }
  return out;
}
 
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
  return out;
}
 
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
  return out;
}
 
function calcMomentum(C, period) {
  const n = C.length;
  if (n < period + 1) return null;
  return C.slice(period).map((c, i) => c - C[i]);
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
 
  if (MACD && MACD.sig.length >= 2) {
    const { line, sig } = MACD;
    const i = sig.length - 1;
    s.macdCrossUp = line[8 + i] > sig[i] && line[8 + i - 1] <= sig[i - 1];
  } else { s.macdCrossUp = false; }
 
  s.ema50_200Bear = !!(E50 && E200 && E50[E50.length-1] < E200[E200.length-1]);
  s.aroonBear = !!(AR && AR.dn.length > 0 && AR.dn[AR.dn.length-1] > AR.up[AR.up.length-1]);
 
  if (ATR && ATR.length >= 20) {
    const win = ATR.slice(-20), mean = win.reduce((a,b)=>a+b,0)/20;
    s.atrHigh = ATR[ATR.length-1] > 1.5 * mean;
  } else { s.atrHigh = false; }
 
  if (MOM && MOM.length >= 3) {
    const l = MOM.length;
    s.momentumAccelBear = MOM[l-1] < MOM[l-2] && MOM[l-2] < MOM[l-3];
  } else { s.momentumAccelBear = false; }
 
  s.mfiOversold = !!(MFI && MFI.length > 0 && MFI[MFI.length-1] < 20);
  s.accDistBear = !!(AD && AD.length >= 2 && AD[AD.length-1] < AD[AD.length-2]);
 
  if (ATR && ATR.length >= 20) {
    const win = ATR.slice(-20), mean = win.reduce((a,b)=>a+b,0)/20, last = ATR[ATR.length-1];
    s.atrNormal = last >= 0.5 * mean && last <= 1.2 * mean;
  } else { s.atrNormal = false; }
 
  s.cciOverbought = !!(CCI && CCI.length > 0 && CCI[CCI.length-1] > 100);
  s.higherHighs   = n >= 3 && H[n-1] > H[n-2] && H[n-2] > H[n-3];
 
  const buyOk  = BUY_COMBO.every(k => s[k] === true);
  const sellOk = SELL_COMBO.every(k => s[k] === true);
 
  return { signals: s, buyOk, sellOk };
}
 
// ================================================================
// FIREBASE
// ================================================================
async function readBin() {
  const r = await axios.get(`${FIREBASE_URL}/crypto.json`, { timeout: 12000 });
  return r.data || { trades: [], signals: [], lastScan: null, stats: {} };
}
 
async function writeBin(data) {
  await axios.put(`${FIREBASE_URL}/crypto.json`, data, {
    headers: { 'Content-Type': 'application/json' },
    timeout: 12000
  });
  return data;
}
 
// ================================================================
// TWELVE DATA FETCH
// ================================================================
async function fetchCandles(symbol) {
  let lastErr;
  for (let attempt = 1; attempt <= 3; attempt++) {
    try {
      const res = await axios.get('https://api.twelvedata.com/time_series', {
        params: { symbol, interval: '4h', outputsize: CANDLES, apikey: TWELVE_KEY, format: 'JSON' },
        timeout: 20000
      });
      if (res.data.status === 'error') throw new Error(`Twelve Data: ${res.data.message}`);
      const vals = res.data.values;
      if (!vals || vals.length < 50) throw new Error(`Not enough candles for ${symbol}: ${vals?.length}`);
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
      if (attempt < 3) { console.warn(`  ⚠️  Retry ${attempt}/3 for ${symbol}: ${e.message}`); await sleep(10000); }
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
    totalTrades: closed.length, wins: 0, losses: 0,
    winRate: null, profitFactor: null, totalPnlPct: 0, maxDrawdown: null,
    currentStreak: 0, currentStreakType: null,
    byDirection: { BUY: { trades:0,wins:0,losses:0,winRate:null }, SELL: { trades:0,wins:0,losses:0,winRate:null } },
    byCrypto: Object.fromEntries(CRYPTOS.map(c => [c, { trades:0,wins:0,losses:0,winRate:null }]))
  };
  if (!closed.length) return st;
  let totalGain=0, totalLoss=0, equity=0, peak=0, maxDD=0;
  for (const t of closed) {
    const win = t.result === 'WIN';
    if (win) { st.wins++;   totalGain += Math.abs(t.pnlPct ?? TP_PCT*100); }
    else     { st.losses++; totalLoss += Math.abs(t.pnlPct ?? SL_PCT*100); }
    st.totalPnlPct += (t.pnlPct ?? 0);
    equity += (t.pnlPct ?? 0);
    if (equity > peak) peak = equity;
    const dd = peak - equity;
    if (dd > maxDD) maxDD = dd;
    if (st.byDirection[t.direction]) {
      st.byDirection[t.direction].trades++;
      if (win) st.byDirection[t.direction].wins++;
      else     st.byDirection[t.direction].losses++;
    }
    if (st.byCrypto[t.crypto]) {
      st.byCrypto[t.crypto].trades++;
      if (win) st.byCrypto[t.crypto].wins++;
      else     st.byCrypto[t.crypto].losses++;
    }
  }
  st.winRate      = Math.round(st.wins / closed.length * 100);
  st.profitFactor = totalLoss > 0 ? parseFloat((totalGain/totalLoss).toFixed(2)) : null;
  st.maxDrawdown  = parseFloat(maxDD.toFixed(2));
  st.totalPnlPct  = parseFloat(st.totalPnlPct.toFixed(2));
  for (const d of ['BUY','SELL']) { const x=st.byDirection[d]; x.winRate=x.trades>0?Math.round(x.wins/x.trades*100):null; }
  for (const c of CRYPTOS) { const x=st.byCrypto[c]; x.winRate=x.trades>0?Math.round(x.wins/x.trades*100):null; }
  if (closed.length > 0) {
    const lastResult = closed[closed.length-1].result;
    let streak = 0;
    for (let i=closed.length-1; i>=0 && closed[i].result===lastResult; i--) streak++;
    st.currentStreak=streak; st.currentStreakType=lastResult;
  }
  return st;
}
 
// ================================================================
// FETCH BOUGIES 15MIN (vérification TP/SL)
// ================================================================
async function fetchCandles30(symbol) {
  let lastErr;
  for (let attempt = 1; attempt <= 3; attempt++) {
    try {
      const res = await axios.get('https://api.twelvedata.com/time_series', {
        params: { symbol, interval: '15min', outputsize: 300, apikey: TWELVE_KEY, format: 'JSON' },
        timeout: 20000
      });
      if (res.data.status === 'error') throw new Error(`Twelve Data: ${res.data.message}`);
      const vals = res.data.values;
      if (!vals || vals.length < 2) throw new Error(`Not enough 15min candles for ${symbol}`);
      return vals.reverse().slice(0, -1);
    } catch (e) {
      lastErr = e;
      if (attempt < 3) await sleep(10000);
    }
  }
  throw lastErr;
}
 
// ================================================================
// MAIN SCAN
// ================================================================
let scanRunning = false;
 
async function runScan() {
  if (scanRunning) { console.log('⚠️  Scan already running — skipped'); return { skipped: true }; }
  scanRunning = true;
  const scanTime = new Date().toISOString();
  console.log(`\n📡 Scan started — ${scanTime}`);
  const newSignals = [], errors = [];
 
  for (const crypto of CRYPTOS) {
    try {
      console.log(`  → ${crypto}`);
      const candles = await fetchCandles(crypto);
      const { signals, buyOk, sellOk } = detectSignals(candles);
      const price = candles[candles.length - 1].close;
      if (buyOk) {
        newSignals.push({ id:uid(), crypto, direction:'BUY', price, sl:parseFloat((price*(1-SL_PCT)).toFixed(8)), tp:parseFloat((price*(1+TP_PCT)).toFixed(8)), triggeredAt:scanTime, signals:BUY_COMBO, details:signals, status:'pending' });
        console.log(`     ✅ BUY signal!`);
      }
      if (sellOk) {
        newSignals.push({ id:uid(), crypto, direction:'SELL', price, sl:parseFloat((price*(1+SL_PCT)).toFixed(8)), tp:parseFloat((price*(1-TP_PCT)).toFixed(8)), triggeredAt:scanTime, signals:SELL_COMBO, details:signals, status:'pending' });
        console.log(`     ✅ SELL signal!`);
      }
      if (!buyOk && !sellOk) console.log(`     ○  No signal`);
      await sleep(13000);
    } catch (e) {
      console.error(`     ❌ ${crypto}: ${e.message}`);
      errors.push({ crypto, error: e.message });
    }
  }
 
  try {
    const data    = await readBin();
    data.lastScan = scanTime;
    data.signals  = newSignals;
 
    const activeTrades30 = (data.trades || []).filter(t => t.result === null);
    if (activeTrades30.length) {
      console.log(`\n🔍 Vérification TP/SL 15min — ${activeTrades30.length} trade(s) actif(s)`);
      let tradesChanged = false;
      for (const trade of activeTrades30) {
        try {
          const tp = parseFloat(trade.tp), sl = parseFloat(trade.sl), en = parseFloat(trade.entryPrice);
          const entryTs = new Date(trade.entryDate).getTime();
          if (isNaN(entryTs)) { console.log(`  ⚠️  ${trade.crypto} — date invalide`); continue; }
          const candles30 = await fetchCandles30(trade.crypto);
          await sleep(13000);
          if (!candles30 || !candles30.length) { console.log(`  ⚠️  ${trade.crypto} — bougies 15min indisponibles`); continue; }
          const postEntry = candles30.filter(c => new Date(c.datetime).getTime() > entryTs);
          if (!postEntry.length) {
            const last = candles30[candles30.length-1];
            console.log(`  ⏸  ${trade.crypto} — en attente bougie 15min post-entrée | TP: ${(Math.abs(last.close-tp)/last.close*100).toFixed(2)}% | SL: ${(Math.abs(last.close-sl)/last.close*100).toFixed(2)}%`);
            continue;
          }
          let closed=false, result=null, closePrice=null, closeDate=null;
          for (const candle of postEntry) {
            const high=parseFloat(candle.high), low=parseFloat(candle.low);
            if (trade.direction==='BUY') {
              if (high>=tp){closed=true;result='WIN';closePrice=tp;closeDate=candle.datetime;break;}
              if (low<=sl){closed=true;result='LOSS';closePrice=sl;closeDate=candle.datetime;break;}
            } else {
              if (low<=tp){closed=true;result='WIN';closePrice=tp;closeDate=candle.datetime;break;}
              if (high>=sl){closed=true;result='LOSS';closePrice=sl;closeDate=candle.datetime;break;}
            }
          }
          if (closed) {
            const pnlPct = parseFloat((trade.direction==='BUY'?(closePrice-en)/en*100:(en-closePrice)/en*100).toFixed(2));
            console.log(`  ${result==='WIN'?'✅':'❌'} ${trade.crypto} ${trade.direction} — ${pnlPct>0?'+':''}${pnlPct}% | 15min: ${closeDate}`);
            const idx = data.trades.findIndex(t => t.id === trade.id);
            if (idx !== -1) { data.trades[idx].exitPrice=closePrice; data.trades[idx].exitDate=new Date(closeDate).toISOString(); data.trades[idx].result=result; data.trades[idx].pnlPct=pnlPct; }
            if (trade.signalId && data.signals) { const sig=data.signals.find(s=>s.id===trade.signalId); if(sig) sig.status='closed'; }
            tradesChanged = true;
          } else {
            const last=postEntry[postEntry.length-1];
            console.log(`  ⏸  ${trade.crypto} ${trade.direction} | ${last.close} | TP ${(Math.abs(last.close-tp)/last.close*100).toFixed(2)}% | SL ${(Math.abs(last.close-sl)/last.close*100).toFixed(2)}% | ${postEntry.length} bougies 15min`);
          }
        } catch (e) { console.error(`  ❌ checkTrades ${trade.crypto}: ${e.message}`); }
      }
      if (tradesChanged) data.stats = recalcStats(data.trades);
    }
 
    await writeBin(data);
    console.log(`✅ Scan done — ${newSignals.length} signal(s), ${errors.length} error(s)\n`);
  } catch (e) {
    console.error(`❌ Firebase write failed: ${e.message}`);
    errors.push({ crypto: 'Firebase', error: e.message });
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
 
app.get('/', (_, res) => {
  res.json({ status:'running', engine:'NEXUS CRYPTO', version:'1.0.0', time:new Date().toISOString(), scanning:scanRunning, cryptos:CRYPTOS, slPct:SL_PCT*100+'%', tpPct:TP_PCT*100+'%', signal:{ buy:'macdCrossUp + ema50_200Bear + aroonBear + atrHigh + momentumAccelBear — WR 63%', sell:'mfiOversold + accDistBear + atrNormal + cciOverbought + higherHighs — WR 62%' } });
});
 
app.get('/health', (_, res) => res.json({ ok:true, time:new Date().toISOString(), scanning:scanRunning }));
 
app.get('/api/scan', async (req, res) => {
  try { const result = await runScan(); res.json({ success:true, ...result }); }
  catch (e) { res.status(500).json({ success:false, error:e.message }); }
});
 
app.get('/api/signals', async (_, res) => {
  try { const data = await readBin(); res.json({ lastScan:data.lastScan, signals:data.signals||[] }); }
  catch (e) { res.status(500).json({ error:e.message }); }
});
 
app.get('/api/trades', async (_, res) => {
  try { const data = await readBin(); res.json({ trades:data.trades||[] }); }
  catch (e) { res.status(500).json({ error:e.message }); }
});
 
app.post('/api/trade', async (req, res) => {
  const { crypto, direction, entryPrice, sl, tp, signalId } = req.body;
  if (!crypto||!direction||entryPrice==null||sl==null||tp==null) return res.status(400).json({ error:'Required fields: crypto, direction, entryPrice, sl, tp' });
  if (!['BUY','SELL'].includes(direction)) return res.status(400).json({ error:'direction must be BUY or SELL' });
  if (!CRYPTOS.includes(crypto)) return res.status(400).json({ error:`crypto must be one of: ${CRYPTOS.join(', ')}` });
  try {
    const data = await readBin();
    const trade = { id:uid(), signalId:signalId||null, crypto, direction, entryPrice:parseFloat(entryPrice), sl:parseFloat(sl), tp:parseFloat(tp), entryDate:new Date().toISOString(), exitDate:null, exitPrice:null, result:null, pnlPct:null };
    const sig = (data.signals||[]).find(s => s.id === signalId);
    if (sig) sig.status = 'taken';
    data.trades.push(trade);
    data.stats = recalcStats(data.trades);
    await writeBin(data);
    res.json({ success:true, trade });
  } catch (e) { res.status(500).json({ error:e.message }); }
});
 
app.put('/api/trade/:id', async (req, res) => {
  const { exitPrice, result } = req.body;
  if (exitPrice==null||!result) return res.status(400).json({ error:'Required fields: exitPrice, result' });
  if (!['WIN','LOSS'].includes(result)) return res.status(400).json({ error:'result must be WIN or LOSS' });
  try {
    const data = await readBin();
    const trade = (data.trades||[]).find(t => t.id===req.params.id);
    if (!trade) return res.status(404).json({ error:'Trade not found' });
    if (trade.result!==null) return res.status(400).json({ error:'Trade already closed' });
    trade.exitPrice = parseFloat(exitPrice);
    trade.exitDate  = new Date().toISOString();
    trade.result    = result;
    const ep=trade.entryPrice, xp=trade.exitPrice;
    trade.pnlPct = parseFloat((trade.direction==='BUY'?(xp-ep)/ep*100:(ep-xp)/ep*100).toFixed(2));
    data.stats = recalcStats(data.trades);
    await writeBin(data);
    res.json({ success:true, trade });
  } catch (e) { res.status(500).json({ error:e.message }); }
});
 
app.get('/api/stats', async (_, res) => {
  try { const data = await readBin(); res.json(data.stats||{}); }
  catch (e) { res.status(500).json({ error:e.message }); }
});
 
// ================================================================
// CRON — toutes les 4h05
// ================================================================
cron.schedule('5 */4 * * *', () => {
  console.log('⏰ Cron triggered — scan toutes les 4h05');
  runScan().catch(e => console.error('Cron scan error:', e.message));
}, { scheduled: true, timezone: 'Europe/Paris' });
 
// ================================================================
// START
// ================================================================
app.listen(PORT, () => {
  console.log(`\n🚀 NEXUS CRYPTO — Port ${PORT}`);
  console.log(`   Firebase  : ${FIREBASE_URL}/crypto`);
  console.log(`   Pairs     : ${CRYPTOS.join(' | ')}`);
  console.log(`   SL / TP   : ${SL_PCT * 100}% / ${TP_PCT * 100}%`);
  console.log(`   Cron      : toutes les 4h05 (Europe/Paris)\n`);
});
 
