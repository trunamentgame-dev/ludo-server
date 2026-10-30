'use strict';
/**
 * Crazy Time authoritative server (single instance). No extra npm package except firebase-admin.
 * - WebSocket (built-in RFC6455) at the same host. Client messages: auth / bet / clear.
 * - Wallet = Firebase RTDB users/{uid}/balance, changed ONLY here with atomic transactions
 *   (balance + idempotency markers czb/czs change in ONE transaction on users/{uid}).
 * - Result = HMAC-SHA256(serverSeed, roundId). sha256(serverSeed) is published when the round opens,
 *   the seed is revealed after settlement. Bets are NEVER read when drawing the result.
 * - payout = bet * multiplier * factor  (TOTAL RETURN incl. stake). Policy B (95%): factor 1 (current paytable = 95% RTP).
 *   Policy A (90%): factor 90/95.
 */
const http = require('http'), crypto = require('crypto');
const PORT = +process.env.PORT || 3000;
const DB_URL = process.env.FIREBASE_DATABASE_URL || 'https://np-trunament-bd-default-rtdb.firebaseio.com';
const SA = process.env.FIREBASE_SERVICE_ACCOUNT || '';
const ORIGINS = (process.env.ALLOWED_ORIGINS || '*').split(',').map((s) => s.trim()).filter(Boolean);
const MIN_BET = +process.env.MIN_BET || 10, MAX_BET = +process.env.MAX_BET || 5000;   // MAX_BET = per spot, per round
const T_BET = 10000, T_SPIN = 8000, T_RES = 5000;                                    // same as client timers

// ---- Paytable (taken from the current game: weights out of 10000, MEGA table out of 1000) ----
const SP = [
  { id: 'x2', label: '2x', m: 2, slots: 4750, segs: 9 }, { id: 'x5', label: '5x', m: 5, slots: 1900, segs: 5 },
  { id: 'x10', label: '10x', m: 10, slots: 950, segs: 3 }, { id: 'x20', label: '20x', m: 20, slots: 475, segs: 2 },
  { id: 'x50', label: '50x', m: 50, slots: 190, segs: 1 }, { id: 'mega', label: 'MEGA', m: null, slots: 1735, segs: 4 }];
const MEGA = [[3, 456], [5, 280], [8, 197], [15, 62], [40, 5]];
const MEGA_AVG = MEGA.reduce((a, [m, w]) => a + m * w, 0) / 1000;
const LAYOUT = (() => { const k = []; SP.forEach((s, si) => { for (let i = 0; i < s.segs; i++) k.push({ id: s.id, key: (i + .5) / s.segs + si * 1e-6 }); }); return k.sort((a, b) => a.key - b.key).map((x) => x.id); })();
const PUB_SPOTS = SP.map((s) => ({ id: s.id, label: s.label, m: s.m, slots: s.slots }));

// ---- Firebase (production) or in-memory (DEV only) ----
let admin = null, db = null;
const dev = !SA; const devUsers = new Map();
if (SA) {
  try { admin = require('firebase-admin'); admin.initializeApp({ credential: admin.credential.cert(JSON.parse(SA)), databaseURL: DB_URL }); db = admin.database(); console.log('Firebase connected'); }
  catch (e) { console.error('Firebase init error', e); process.exit(1); }
} else if (process.env.NODE_ENV === 'production') { console.error('FIREBASE_SERVICE_ACCOUNT required'); process.exit(1); }
else console.warn('DEV MODE: in-memory wallet (1000), token format dev:<uid>. NEVER use in production.');
const r2 = (n) => Math.round(n * 100) / 100, sha = (s) => crypto.createHash('sha256').update(s).digest('hex');
const dbw = (fn) => { if (!db) return Promise.resolve(); try { return Promise.resolve(fn(db)).catch((e) => console.error('db write', e.message)); } catch (e) { return Promise.resolve(); } };

// Atomic change of users/{uid}. fn(cur) -> {val,out} | {err}
async function utx(uid, fn) {
  try {
    if (dev) { const cur = JSON.parse(JSON.stringify(devUsers.get(uid) || { balance: 1000 })); const n = fn(cur); if (n.err) return n; devUsers.set(uid, n.val); return n.out; }
    const ref = db.ref('users/' + uid); await ref.once('value'); const o = {};
    await ref.transaction((cur) => { o.v = null; if (cur === null) { o.v = { err: 'NO_USER' }; return; } const n = fn(cur); if (n.err) { o.v = n; return; } o.v = n.out; return n.val; });
    return o.v || { err: 'TXN' };
  } catch (e) { console.error('utx', uid, e.message); return { err: 'TXN' }; }
}
const bal = (c) => Number(c.balance) || 0;
const betFn = (id, amt) => (c) => { const z = c.czb || {}; if (z[id]) return { val: c, out: { ok: true, bal: bal(c) } }; if (bal(c) < amt) return { err: 'INSUFFICIENT' }; const nb = r2(bal(c) - amt); return { val: { ...c, balance: nb, czb: { ...z, [id]: amt } }, out: { ok: true, bal: nb } }; };
const undoFn = (id) => (c) => { const z = { ...(c.czb || {}) }; const a = z[id]; if (!a) return { val: c, out: { ok: true, bal: bal(c) } }; delete z[id]; const nb = r2(bal(c) + a); return { val: { ...c, balance: nb, czb: z }, out: { ok: true, bal: nb } }; };
// settle (winOf = amount actually deducted for these bets -> payout) or refund. Once per round (czs marker).
const closeFn = (rid, ids, winOf) => (c) => {
  const s = { ...(c.czs || {}) }; if (s[rid]) return { val: c, out: { dup: true, bal: bal(c) } };
  const z = { ...(c.czb || {}) }; let ded = 0; ids.forEach((i) => { if (z[i]) { ded += z[i]; delete z[i]; } });
  const win = r2(winOf(ded)); const ks = Object.keys(s).sort(); while (ks.length >= 30) delete s[ks.shift()]; s[rid] = 1;
  return { val: { ...c, balance: r2(bal(c) + win), czb: z, czs: s }, out: { ok: true, bal: r2(bal(c) + win), win } };
};

// ---- Game state ----
let R = null, seq = 0, cfgPolicy = 'B', history = [], liveDirty = true;
const clients = new Set();
if (db) db.ref('crazytime_config/policy').on('value', (s) => { const v = s.val(); if (v === 'A' || v === 'B') cfgPolicy = v; });
const factorOf = (p) => (p === 'A' ? 90 / 95 : 1);

function draw(seed, id) {
  const h = crypto.createHmac('sha256', seed).update(id).digest(), u = (o) => h.readUInt32BE(o) / 4294967296;
  const x = Math.floor(u(0) * 10000); let a = 0, spot = 'mega';
  for (const s of SP) { a += s.slots; if (x < a) { spot = s.id; break; } }
  let mega = null; if (spot === 'mega') { const y = Math.floor(u(4) * 1000); let b = 0; for (const [m, w] of MEGA) { b += w; if (y < b) { mega = m; break; } } }
  const idx = LAYOUT.map((id2, i) => (id2 === spot ? i : -1)).filter((i) => i >= 0);
  return { spot, mega, seg: idx[Math.floor(u(8) * idx.length)] };
}
function newRound() {
  seq++; const seed = crypto.randomBytes(32).toString('hex');
  R = { id: `ct_${Date.now()}_${seq}`, seed, commit: sha(seed), phase: 'betting', endsAt: Date.now() + T_BET, policy: cfgPolicy, bets: new Map(), mine: new Map(), keys: new Set(), totals: {}, n: 0, result: null, settling: false };
  dbw((d) => d.ref('crazytime_rounds/' + R.id).set({ commit: R.commit, status: 'betting', policy: R.policy, startedAt: Date.now() }));
  broadcastState(); liveDirty = true;
}
const maskName = (n) => { n = String(n || 'user').split('@')[0]; return n.length <= 3 ? n[0] + '***' : n.slice(0, 2) + '***' + n.slice(-1); };
function publicState(extra) {
  const r = R, s = { t: 'state', phase: r.phase, roundId: r.id, endsAt: r.endsAt, now: Date.now(), online: online(), cfg: { minBet: MIN_BET, maxBet: MAX_BET }, history, commit: r.commit };
  if (r.result && (r.phase === 'spin' || r.phase === 'result')) s.result = r.result;
  if (r.phase === 'result') s.seed = r.seed; return s;
}
const online = () => { let n = 0; clients.forEach((c) => { if (c.uid) n++; }); return n; };
function send(c, o) { if (!c.sock.destroyed) frame(c.sock, 1, Buffer.from(JSON.stringify(o))); }
function toUid(uid, o) { clients.forEach((c) => { if (c.uid === uid) send(c, o); }); }
function broadcast(o) { const b = Buffer.from(JSON.stringify(o)); clients.forEach((c) => { if (c.uid && !c.sock.destroyed) frame(c.sock, 1, b); }); }
function broadcastState() { broadcast(publicState()); }
const myBets = (uid) => ({ ...(R.mine.get(uid) || {}) });

async function onBet(c, m) {
  const r = R;
  if (!r || r.phase !== 'betting' || Date.now() >= r.endsAt) return send(c, { t: 'err', msg: 'বেটিং বন্ধ আছে' });
  const spot = String(m.spot), amt = Math.floor(Number(m.amount)), key = String(m.key || '').slice(0, 64);
  if (!SP.some((s) => s.id === spot) || !Number.isFinite(amt) || amt < MIN_BET || amt > MAX_BET) return send(c, { t: 'err', msg: 'অবৈধ বেট' });
  if (key) { if (r.keys.has(c.uid + key)) return; r.keys.add(c.uid + key); }
  const mine = r.mine.get(c.uid) || {};
  if ((mine[spot] || 0) + amt > MAX_BET) return send(c, { t: 'err', msg: 'এই ঘরে সর্বোচ্চ বেট সীমা পূর্ণ' });
  r.mine.set(c.uid, { ...mine, [spot]: (mine[spot] || 0) + amt });   // reserve (concurrency)
  const rollback = () => { const x = r.mine.get(c.uid) || {}; x[spot] = Math.max(0, (x[spot] || 0) - amt); r.mine.set(c.uid, x); };
  const id = `${r.id}:${c.uid}:${++r.n}`;
  await dbw((d) => d.ref(`crazytime_active/${r.id}/${id}`).set({ uid: c.uid, amount: amt }));
  const o = await utx(c.uid, betFn(id, amt));
  if (!o.ok) { rollback(); dbw((d) => d.ref(`crazytime_active/${r.id}/${id}`).remove()); return send(c, { t: 'err', msg: o.err === 'INSUFFICIENT' ? 'ব্যালেন্স যথেষ্ট নয়' : 'বেট ব্যর্থ, আবার চেষ্টা করুন' }); }
  if (R !== r || r.phase !== 'betting') { const u = await utx(c.uid, undoFn(id)); rollback(); dbw((d) => d.ref(`crazytime_active/${r.id}/${id}`).remove()); send(c, { t: 'err', msg: 'বেটিং বন্ধ হয়ে গেছে, টাকা ফেরত' }); if (u.ok) toUid(c.uid, { t: 'bal', balance: u.bal }); return; }
  r.bets.set(id, { uid: c.uid, spot, amount: amt, ts: Date.now() }); r.totals[spot] = r2((r.totals[spot] || 0) + amt); liveDirty = true;
  toUid(c.uid, { t: 'bal', balance: o.bal }); toUid(c.uid, { t: 'bets', bets: myBets(c.uid) });
  dbw((d) => d.ref('game_transactions/' + id.replace(/[.#$\[\]\/]/g, '_')).set({ type: 'bet', game: 'CrazyTime', uid: c.uid, amount: amt, spot, round: r.id, betId: id, balance: o.bal, time: Date.now() }));
}
async function onClear(c) {
  const r = R; if (!r || r.phase !== 'betting') return;
  const ids = [...r.bets].filter(([, b]) => b.uid === c.uid); let last = null;
  for (const [id, b] of ids) { if (R !== r || r.phase !== 'betting') break; const u = await utx(c.uid, undoFn(id)); if (!u.ok) continue; r.bets.delete(id); r.totals[b.spot] = r2(Math.max(0, (r.totals[b.spot] || 0) - b.amount)); last = u.bal; dbw((d) => d.ref(`crazytime_active/${r.id}/${id}`).remove()); dbw((d) => d.ref('game_transactions/' + (id + '_cancel').replace(/[.#$\[\]\/]/g, '_')).set({ type: 'bet_cancel', game: 'CrazyTime', uid: c.uid, amount: b.amount, round: r.id, betId: id, balance: u.bal, time: Date.now() })); }
  const left = {}; r.bets.forEach((b) => { if (b.uid === c.uid) left[b.spot] = (left[b.spot] || 0) + b.amount; }); r.mine.set(c.uid, left); liveDirty = true;
  if (last !== null) toUid(c.uid, { t: 'bal', balance: last }); toUid(c.uid, { t: 'bets', bets: left });
}

function closeBets() {
  const r = R; r.phase = 'spin'; r.result = draw(r.seed, r.id); r.endsAt = Date.now() + T_SPIN;
  dbw((d) => d.ref('crazytime_rounds/' + r.id).update({ status: 'spinning', closedAt: Date.now() }));
  broadcastState(); liveDirty = true;
}
async function settle(r) {
  const res = r.result, f = factorOf(r.policy), m = res.spot === 'mega' ? res.mega : SP.find((s) => s.id === res.spot).m;
  const per = new Map(); let totalBet = 0, onWin = 0;
  r.bets.forEach((b, id) => { let u = per.get(b.uid); if (!u) per.set(b.uid, u = { ids: [], stake: 0, win: 0, bets: {} }); u.ids.push(id); u.stake += b.amount; u.bets[b.spot] = (u.bets[b.spot] || 0) + b.amount; totalBet += b.amount; if (b.spot === res.spot) { u.win += b.amount * m * f; onWin += b.amount; } });
  let totalWin = 0; const winners = [];
  await Promise.all([...per].map(async ([uid, u]) => {
    u.win = r2(u.win); let o;
    for (let i = 0; i < 3; i++) { o = await utx(uid, closeFn(r.id, u.ids, () => u.win)); if (!o.err) break; await new Promise((s) => setTimeout(s, 300)); }
    if (o.err) { dbw((d) => d.ref(`crazytime_failed/${r.id}_${uid}`).set({ uid, round: r.id, win: u.win, stake: u.stake, error: o.err, time: Date.now() })); return; }
    if (o.dup) return; totalWin = r2(totalWin + u.win);
    toUid(uid, { t: 'bal', balance: o.bal }); toUid(uid, { t: 'settle', roundId: r.id, stake: u.stake, win: u.win, spot: res.spot, mega: res.mega });
    if (u.win > 0) { const cl = [...clients].find((x) => x.uid === uid); winners.push({ name: maskName(cl ? cl.name : uid), win: u.win }); }
    dbw((d) => d.ref(`crazytime_user_bets/${uid}/${r.id}`).set({ round: r.id, bets: u.bets, stake: u.stake, win: u.win, spot: res.spot, mega: res.mega, time: Date.now() }));
    dbw((d) => d.ref(`game_transactions/${r.id}_${uid}_settle`.replace(/[.#$\[\]\/]/g, '_')).set({ type: u.win > 0 ? 'win' : 'loss', game: 'CrazyTime', uid, amount: u.stake, win: u.win, round: r.id, balance: o.bal, time: Date.now() }));
  }));
  const stats = { round: r.id, policy: r.policy, result: res, totals: r.totals, bettors: per.size, totalBet: r2(totalBet), totalWin, totalLosing: r2(totalBet - onWin), houseRevenue: r2(totalBet - totalWin), time: Date.now() };
  await dbw((d) => d.ref('crazytime_rounds/' + r.id).update({ status: 'settled', result: res, serverSeed: r.seed, settledAt: Date.now() }));
  dbw((d) => d.ref('crazytime_round_stats/' + r.id).set(stats));
  dbw((d) => d.ref('adminAuditLogs/ct_' + r.id).set({ action: 'crazytime_settlement', admin: 'SYSTEM', details: `Round ${r.id} result=${res.spot}${res.mega ? ' ' + res.mega + 'x' : ''} bet=${stats.totalBet} paid=${totalWin} house=${stats.houseRevenue} policy=${r.policy}`, timestamp: Date.now() }));
  dbw((d) => d.ref('crazytime_active/' + r.id).remove());
  console.log('ROUND', JSON.stringify(stats)); return winners.sort((a, b) => b.win - a.win).slice(0, 10);
}
async function finish(r) {
  let winners = []; try { winners = await settle(r); } catch (e) { console.error('settle error', e); }
  history = [{ id: r.id, spot: r.result.spot, mega: r.result.mega }, ...history].slice(0, 20);
  r.phase = 'result'; r.endsAt = Date.now() + T_RES; broadcastState(); if (winners.length) broadcast({ t: 'winners', list: winners }); liveDirty = true;
}
setInterval(() => {
  if (!R) return; const now = Date.now();
  if (R.phase === 'betting' && now >= R.endsAt) closeBets();
  else if (R.phase === 'spin' && now >= R.endsAt && !R.settling) { R.settling = true; finish(R); }
  else if (R.phase === 'result' && now >= R.endsAt) newRound();
}, 100);
setInterval(() => {   // admin live snapshot + online count
  if (!R || !liveDirty) return; liveDirty = false; const f = factorOf(R.policy); let tb = 0, pot = {};
  SP.forEach((s) => { const t = R.totals[s.id] || 0; tb += t; pot[s.id] = r2(t * (s.m || MEGA_AVG) * f); });
  dbw((d) => d.ref('crazytime_live').set({ roundId: R.id, phase: R.phase, endsAt: R.endsAt, policy: R.policy, totals: R.totals, totalBet: r2(tb), potentialPayout: pot, megaAvg: MEGA_AVG, bettors: new Set([...R.bets.values()].map((b) => b.uid)).size, online: online(), updated: Date.now() }));
}, 1000);
setInterval(() => { liveDirty = true; if (R && R.phase === 'betting') broadcastState(); }, 5000);   // refresh online counter
setInterval(() => clients.forEach((c) => { if (!c.sock.destroyed) frame(c.sock, 9, Buffer.alloc(0)); }), 25000);

async function recover() {   // after crash/restart: refund every bet of unsettled rounds (marker makes it safe/once)
  if (!db) return; const all = (await db.ref('crazytime_active').once('value')).val() || {};
  for (const rid of Object.keys(all)) {
    const per = {}; Object.entries(all[rid]).forEach(([id, b]) => { (per[b.uid] = per[b.uid] || []).push(id); });
    for (const uid of Object.keys(per)) { const o = await utx(uid, closeFn(rid, per[uid], (d) => d)); if (o && o.ok && !o.dup) await dbw((d) => d.ref(`game_transactions/${rid}_${uid}_refund`.replace(/[.#$\[\]\/]/g, '_')).set({ type: 'refund', game: 'CrazyTime', uid, amount: o.win, round: rid, reason: 'server_restart', time: Date.now() })); }
    await dbw((d) => d.ref('crazytime_rounds/' + rid).update({ status: 'cancelled_refunded' }));
    await dbw((d) => d.ref('crazytime_active/' + rid).remove());
    await dbw((d) => d.ref('adminAuditLogs/ct_recover_' + rid).set({ action: 'crazytime_recover_refund', admin: 'SYSTEM', details: 'Unsettled round refunded after restart: ' + rid, timestamp: Date.now() }));
    console.log('RECOVERED round', rid);
  }
}

// ---- Auth ----
async function auth(c, token) {
  let uid, name = 'user';
  try {
    if (dev && String(token).startsWith('dev:')) uid = String(token).slice(4);
    else { const d = await admin.auth().verifyIdToken(String(token)); uid = d.uid; name = d.name || d.email || 'user'; }
    if (!uid || uid.length > 128 || /[.#$\[\]\/]/.test(uid)) throw new Error('bad uid');
  } catch (e) { send(c, { t: 'fatal', msg: 'লগইন যাচাই ব্যর্থ। ইউজার প্যানেল থেকে আবার Play Now চাপুন।' }); return c.sock.end(); }
  c.uid = uid; c.name = name;
  if (!db) name = uid;
  if (db) { try { const n = (await db.ref(`users/${uid}/name`).once('value')).val(); if (n) c.name = n; } catch (e) {} }
  const b = await utx(uid, (cur) => ({ val: cur, out: { ok: true, bal: bal(cur) } }));
  send(c, { t: 'hello', layout: LAYOUT, spots: PUB_SPOTS, bets: myBets(uid) });
  send(c, { t: 'bal', balance: b.ok ? b.bal : 0 }); send(c, publicState()); broadcastState();
}
function onMsg(c, txt) {
  let m; try { m = JSON.parse(txt); } catch (e) { return; }
  const now = Date.now(); if (now - c.t > 1000) { c.t = now; c.cnt = 0; } if (++c.cnt > 30) return;
  if (m.t === 'auth') { if (!c.uid) c.q = c.q.then(() => auth(c, m.token)); return; }
  if (!c.uid) return;
  if (m.t === 'bet') c.q = c.q.then(() => onBet(c, m)).catch((e) => console.error(e)); else if (m.t === 'clear') c.q = c.q.then(() => onClear(c)).catch((e) => console.error(e));
}

// ---- Minimal WebSocket (RFC6455, text frames) ----
function frame(sock, op, p) {
  let h; if (p.length < 126) h = Buffer.from([0x80 | op, p.length]); else if (p.length < 65536) { h = Buffer.alloc(4); h[0] = 0x80 | op; h[1] = 126; h.writeUInt16BE(p.length, 2); } else { h = Buffer.alloc(10); h[0] = 0x80 | op; h[1] = 127; h.writeBigUInt64BE(BigInt(p.length), 2); }
  try { sock.write(Buffer.concat([h, p])); } catch (e) {}
}
const server = http.createServer((req, res) => {
  res.setHeader('Access-Control-Allow-Origin', '*');
  if (req.url === '/' || req.url === '/health') { res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ ok: true, game: 'crazytime', round: R && R.id, phase: R && R.phase, online: online() })); }
  res.writeHead(404); res.end();
});
server.on('upgrade', (req, sock) => {
  const origin = req.headers.origin, key = req.headers['sec-websocket-key'];
  if (!key || (!ORIGINS.includes('*') && origin && !ORIGINS.includes(origin))) return sock.destroy();
  sock.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + crypto.createHash('sha1').update(key + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64') + '\r\n\r\n');
  const c = { sock, uid: null, name: '', buf: Buffer.alloc(0), q: Promise.resolve(), t: 0, cnt: 0 }; clients.add(c);
  const drop = () => { if (clients.delete(c)) liveDirty = true; };
  sock.on('close', drop); sock.on('error', () => { drop(); sock.destroy(); });
  sock.on('data', (d) => {
    c.buf = Buffer.concat([c.buf, d]); if (c.buf.length > 65536) return sock.destroy();
    for (;;) {
      const b = c.buf; if (b.length < 2) break; const op = b[0] & 15, mk = !!(b[1] & 128); let len = b[1] & 127, off = 2;
      if (len === 126) { if (b.length < 4) break; len = b.readUInt16BE(2); off = 4; } else if (len === 127) { if (b.length < 10) break; len = Number(b.readBigUInt64BE(2)); off = 10; }
      if (len > 16384) return sock.destroy(); const hl = off + (mk ? 4 : 0); if (b.length < hl + len) break;
      let p = b.subarray(hl, hl + len); if (mk) { const k = b.subarray(off, off + 4); p = Buffer.from(p); for (let i = 0; i < p.length; i++) p[i] ^= k[i & 3]; }
      c.buf = b.subarray(hl + len);
      if (op === 8) return sock.end(); if (op === 9) frame(sock, 10, p); else if (op === 1) onMsg(c, p.toString());
    }
  });
});
recover().catch((e) => console.error('recover', e)).then(() => { newRound(); server.listen(PORT, () => console.log('Crazy Time server on ' + PORT)); });
