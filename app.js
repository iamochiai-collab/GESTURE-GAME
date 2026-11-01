/* ジェスチャーパーティー
 * - Firebase Realtime Database でオンライン同期（未設定ならデモモード）
 * - 個人戦 / チーム戦、答え方（入力・声・両方）、タイムアタック2種
 */
(() => {
'use strict';

// ===================== 設定 =====================
const MAX_PLAYERS = 10;
const ROOM_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
const EMOJIS = ['🐶','🐱','🐼','🦊','🐸','🐵','🐯','🐰','🐻','🐨','🐷','🐮','🐔','🐧','🦁','🐙','🦄','🐳','🦖','🐝'];
const TEAM = { red:{ name:'あかチーム' }, blue:{ name:'あおチーム' } };
const GENRES = window.GENRES || [];
const DEFAULT_SETTINGS = {
  battle:'solo', answer:'both', timeMode:'limit', limitSec:60, target:5, targetMax:180, turnsEach:1,
  genres: Object.fromEntries(GENRES.map(g => [g.id, true]))
};
const SETTING_ROWS = [
  { key:'battle', label:'対戦', opts:[['solo','個人戦'],['team','チーム戦']],
    help:s => s.battle === 'solo' ? '演じる人と当てた人に1点ずつ。' : '同じチームの人だけが答えられます。' },
  { key:'answer', label:'答え方', opts:[['type','入力'],['voice','声'],['both','両方']],
    help:s => ({ type:'自分のスマホに答えを入力 → 自動で判定。', voice:'口で答えて、演じる人が「正解」ボタンをおす。', both:'入力でも声でもOK。' })[s.answer] },
  { key:'timeMode', label:'タイムアタック', opts:[['limit','時間内に何問？'],['target','何問を何秒で？']],
    help:s => s.timeMode === 'limit' ? '制限時間内に当ててもらえた数をきそう。' : '決めた数を当ててもらうまでのタイムをきそう（最大3分）。' },
  { key:'limitSec', label:'制限時間', show:s => s.timeMode === 'limit', time:true },
  { key:'target', label:'目標', show:s => s.timeMode === 'target', opts:[[3,'3問'],[5,'5問'],[10,'10問']] },
  { key:'turnsEach', label:'1人が演じる回数', opts:[[1,'1回'],[2,'2回'],[3,'3回']] },
];

const app = document.getElementById('app');
const S = {
  db:null, local:false, roomId:null, pendingRoom:null, pid:null, room:null, unsub:null,
  joined:false, presenceSet:false, screenKey:'', busy:false, busyWord:null, ending:null,
  processed:new Set(), deckCache:null, sound:true, lastCount:null, lastWarn:null,
  prevPhase:null, prevLogKey:'', toastTimer:null,
};

// ===================== 小さな道具 =====================
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;' }[c]));
const store = {
  get(k){ try { return localStorage.getItem(k); } catch(e){ return null; } },
  set(k, v){ try { v == null ? localStorage.removeItem(k) : localStorage.setItem(k, v); } catch(e){} }
};
function rid(n, chars = 'abcdefghijkmnpqrstuvwxyz23456789'){
  const a = new Uint32Array(n); crypto.getRandomValues(a);
  let s = ''; for (const x of a) s += chars[x % chars.length]; return s;
}
// プレイヤーIDの保存先：本番は localStorage（再読み込みしても同じ人）、デモはタブごとに別人にする
const pidStore = {
  get(id){ try { return (S.local ? sessionStorage : localStorage).getItem('gesture-pid-' + id); } catch(e){ return null; } },
  set(id, v){ try { const st = S.local ? sessionStorage : localStorage; v == null ? st.removeItem('gesture-pid-' + id) : st.setItem('gesture-pid-' + id, v); } catch(e){} }
};
const newKey = () => Date.now().toString(36) + rid(6);
const vals = o => Object.values(o || {}).filter(Boolean);
function mulberry32(a){ return function(){ a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
function shuffle(arr, rnd = Math.random){ const a = arr.slice(); for (let i = a.length - 1; i > 0; i--){ const j = Math.floor(rnd() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; }
// 答えのゆれを吸収：全角半角・カタカナ→ひらがな・記号や長音をのぞく
function norm(s){
  return String(s || '').normalize('NFKC').toLowerCase()
    .replace(/[ァ-ヶ]/g, c => String.fromCharCode(c.charCodeAt(0) - 0x60))
    .replace(/[\s　・･、。,.!?！？「」『』ー\-~〜"'`]/g, '');
}
const fmtSec = x => (Math.round((x || 0) * 10) / 10).toFixed(1);
// 制限時間は 1分〜10分、10秒きざみ
const TIME_MIN = 60, TIME_MAX = 600;
const clampLimit = v => Math.min(TIME_MAX, Math.max(TIME_MIN, Math.round((Number(v) || 60) / 10) * 10));
const fmtClock = sec => `${Math.floor(sec / 60)}:${String(sec % 60).padStart(2, '0')}`;
const fmtJa = sec => { const m = Math.floor(sec / 60), s = sec % 60; return `${m}分${s ? s + '秒' : ''}`; };
function toast(msg){
  const t = document.getElementById('toast'); t.textContent = msg; t.classList.add('show');
  clearTimeout(S.toastTimer); S.toastTimer = setTimeout(() => t.classList.remove('show'), 2400);
}
function rainbow(text){
  const cols = ['#ff5c8a','#ff9f1c','#ffd23f','#2ec4b6','#3a86ff','#8338ec']; let i = 0;
  return [...text].map(ch => ch === '\n' ? '<br>' : `<span style="color:${cols[i++ % cols.length]}">${esc(ch)}</span>`).join('');
}
function popEmoji(e){
  const d = document.createElement('div'); d.className = 'pop-emoji'; d.textContent = e;
  document.body.appendChild(d); setTimeout(() => d.remove(), 1000);
}
const baseUrl = () => location.href.split('?')[0].split('#')[0];
const roomUrl = () => baseUrl() + '?r=' + S.roomId;

// ===================== 効果音 =====================
let actx = null;
function unlockAudio(){
  if (!actx){ try { actx = new (window.AudioContext || window.webkitAudioContext)(); } catch(e){} }
  if (actx && actx.state === 'suspended') actx.resume();
}
function beep(type){
  if (!S.sound || !actx) return;
  const seq = { tick:[[660,.09]], go:[[880,.1],[1320,.2]], ok:[[784,.08],[1046,.08],[1318,.18]],
    pass:[[330,.12]], end:[[523,.14],[392,.14],[262,.3]], warn:[[1000,.05]], win:[[523,.1],[659,.1],[784,.1],[1046,.3]] }[type];
  if (!seq) return;
  let t = actx.currentTime;
  for (const [f, d] of seq){
    const o = actx.createOscillator(), g = actx.createGain();
    o.type = 'triangle'; o.frequency.value = f;
    g.gain.setValueAtTime(0.22, t); g.gain.exponentialRampToValueAtTime(0.001, t + d);
    o.connect(g).connect(actx.destination); o.start(t); o.stop(t + d + 0.02); t += d;
  }
}

// ===================== データベース =====================
async function initDB(){
  const cfg = window.FIREBASE_CONFIG || {};
  if (cfg.apiKey && cfg.databaseURL){
    try { S.db = await firebaseDB(cfg); return; } catch(e){ console.error('Firebaseに接続できませんでした', e); }
  }
  S.local = true; S.db = localDB();
}

async function firebaseDB(cfg){
  const V = '10.12.2';
  const [{ initializeApp }, F] = await Promise.all([
    import(`https://www.gstatic.com/firebasejs/${V}/firebase-app.js`),
    import(`https://www.gstatic.com/firebasejs/${V}/firebase-database.js`)
  ]);
  const db = F.getDatabase(initializeApp(cfg));
  let offset = 0;
  F.onValue(F.ref(db, '.info/serverTimeOffset'), s => { offset = s.val() || 0; });
  return {
    get: async p => (await F.get(F.ref(db, p))).val(),
    set: (p, v) => F.set(F.ref(db, p), v),
    update: (p, o) => F.update(F.ref(db, p), o),
    on: (p, cb) => F.onValue(F.ref(db, p), s => cb(s.val())),
    presence(p, isActive){
      F.onValue(F.ref(db, '.info/connected'), s => {
        if (s.val() !== true || !isActive()) return;
        F.onDisconnect(F.ref(db, p)).update({ online:false }).then(() => {
          if (isActive()) F.update(F.ref(db, p), { online:true });
        });
      });
    },
    cancelPresence: p => F.onDisconnect(F.ref(db, p)).cancel(),
    now: () => Date.now() + offset,
  };
}

// デモモード：localStorage を共有して、同じブラウザのタブ同士で同期
function localDB(){
  const KEY = 'gesture-local-db-v1';
  const read = () => { try { return JSON.parse(localStorage.getItem(KEY)) || {}; } catch(e){ return {}; } };
  let data = read();
  const listeners = new Set();
  const parts = p => p.split('/').filter(Boolean);
  const getAt = p => { let o = data; for (const k of parts(p)){ if (o == null || typeof o !== 'object') return null; o = o[k]; } return o === undefined ? null : o; };
  const setAt = (p, v) => {
    const ks = parts(p);
    if (!ks.length){ data = v ?? {}; return; }
    let o = data; const stack = [];
    for (let i = 0; i < ks.length - 1; i++){
      const k = ks[i];
      if (o[k] == null || typeof o[k] !== 'object') o[k] = {};
      stack.push([o, k]); o = o[k];
    }
    const last = ks[ks.length - 1];
    if (v === null || v === undefined) delete o[last]; else o[last] = JSON.parse(JSON.stringify(v));
    for (let i = stack.length - 1; i >= 0; i--){
      const [po, k] = stack[i];
      if (po[k] && typeof po[k] === 'object' && !Object.keys(po[k]).length) delete po[k];
    }
  };
  function notify(){
    for (const l of listeners){
      const s = JSON.stringify(getAt(l.p));
      if (s !== l.last){ l.last = s; l.cb(JSON.parse(s)); }
    }
  }
  let pending = false, ch = null;
  try { ch = new BroadcastChannel('gesture-local'); ch.onmessage = () => { data = read(); notify(); }; } catch(e){}
  window.addEventListener('storage', e => { if (e.key === KEY){ data = read(); notify(); } });
  const commit = () => {
    try { localStorage.setItem(KEY, JSON.stringify(data)); } catch(e){}
    if (ch) ch.postMessage(1);
    if (!pending){ pending = true; queueMicrotask(() => { pending = false; notify(); }); }
  };
  return {
    get: async p => { data = read(); return JSON.parse(JSON.stringify(getAt(p))); },
    set: async (p, v) => { data = read(); setAt(p, v); commit(); },
    update: async (p, o) => { data = read(); for (const [k, v] of Object.entries(o)) setAt(p + '/' + k, v); commit(); },
    on(p, cb){
      const l = { p, cb, last:undefined }; listeners.add(l);
      queueMicrotask(() => { l.last = JSON.stringify(getAt(p)); cb(JSON.parse(l.last)); });
      return () => listeners.delete(l);
    },
    presence(p, isActive){
      window.addEventListener('pagehide', () => {
        if (!isActive()) return;
        data = read(); if (getAt(p)){ setAt(p + '/online', false); try { localStorage.setItem(KEY, JSON.stringify(data)); } catch(e){} }
      });
    },
    cancelPresence(){},
    now: () => Date.now(),
  };
}

const upd = o => S.db.update(`rooms/${S.roomId}`, o).catch(e => { console.error(e); toast('通信エラーが起きました'); });

// ===================== 状態の読み取り =====================
const R = () => S.room || {};
const G = () => R().game || { phase:'lobby' };
const P = () => R().players || {};
const me = () => { const p = P()[S.pid]; return p && p.name ? p : null; };
const isHost = () => !!(R().meta && R().meta.hostId === S.pid);
const settings = () => ({ ...DEFAULT_SETTINGS, ...(R().settings || {}) });
const playerList = () => Object.entries(P()).filter(([, p]) => p && p.name)
  .map(([id, p]) => ({ id, ...p })).sort((a, b) => (a.joinedAt || 0) - (b.joinedAt || 0));
const onlinePlayers = () => playerList().filter(p => p.online);
const pName = id => { const p = P()[id]; return p && p.name ? p.name : '？？？'; };
const pEmoji = id => { const p = P()[id]; return p && p.emoji ? p.emoji : '🙂'; };

function canGuess(pid){
  const g = G(); if (!g.cfg || pid === g.actorId) return false;
  const p = P()[pid]; if (!p || !p.name) return false;
  return g.cfg.battle === 'solo' || p.team === g.actorTeam;
}

function deckFor(g){
  const c = g.cfg || DEFAULT_SETTINGS;
  const ids = GENRES.filter(x => c.genres && c.genres[x.id]).map(x => x.id);
  const key = g.seed + ':' + ids.join(',');
  if (S.deckCache && S.deckCache.key === key) return S.deckCache.deck;
  const pool = [];
  for (const gen of GENRES){
    if (!ids.includes(gen.id)) continue;
    for (const w of gen.words){
      const ps = w.split('|');
      pool.push({ display:ps[0], answers:ps.map(norm).filter(Boolean), genre:gen.name, icon:gen.icon });
    }
  }
  const deck = shuffle(pool, mulberry32(g.seed || 1));
  S.deckCache = { key, deck };
  return deck;
}
function currentWord(){
  const g = G(); const d = deckFor(g);
  return d.length ? d[(g.deckPos || 0) % d.length] : null;
}
const judge = (text, w) => { const n = norm(text); return !!n && w.answers.includes(n); };

// ===================== 部屋に入る =====================
async function uniqueRoomId(){
  for (let i = 0; i < 8; i++){
    const id = rid(5, ROOM_CHARS);
    if (!(await S.db.get(`rooms/${id}/meta`))) return id;
  }
  return rid(6, ROOM_CHARS);
}
function pickEmoji(ps){
  const used = new Set(vals(ps).map(p => p.emoji));
  const free = EMOJIS.filter(e => !used.has(e));
  return shuffle(free.length ? free : EMOJIS)[0];
}
function smallerTeam(ps){
  const list = vals(ps).filter(p => p.name && p.online);
  const r = list.filter(p => p.team === 'red').length, b = list.filter(p => p.team === 'blue').length;
  return r <= b ? 'red' : 'blue';
}

async function createRoom(name){
  const id = await uniqueRoomId();
  S.pid = rid(10); pidStore.set(id, S.pid);
  const now = S.db.now();
  await S.db.set(`rooms/${id}`, {
    meta:{ hostId:S.pid, createdAt:now },
    settings:DEFAULT_SETTINGS,
    game:{ phase:'lobby' },
    players:{ [S.pid]:{ name, emoji:pickEmoji({}), team:'red', score:0, online:true, joinedAt:now } }
  });
  enterRoom(id);
}

async function joinRoom(id, name){
  const room = await S.db.get(`rooms/${id}`);
  if (!room || !room.meta){
    S.pendingRoom = null; history.replaceState(null, '', baseUrl());
    render(); toast('部屋が見つかりませんでした'); return;
  }
  const ps = room.players || {};
  let pid = pidStore.get(id);
  const existing = pid && ps[pid] && ps[pid].name ? ps[pid] : null;
  const count = vals(ps).filter(p => p.name && p.online).length;
  if (!existing && count >= MAX_PLAYERS){ toast(`満員です（${MAX_PLAYERS}人まで）`); return; }
  if (!pid){ pid = rid(10); pidStore.set(id, pid); }
  S.pid = pid;
  await S.db.update(`rooms/${id}/players/${pid}`, {
    name,
    emoji: existing ? existing.emoji : pickEmoji(ps),
    team: existing ? existing.team : smallerTeam(ps),
    score: existing ? (existing.score || 0) : 0,
    online: true,
    joinedAt: existing ? existing.joinedAt : S.db.now(),
  });
  enterRoom(id);
}

function enterRoom(id){
  S.pendingRoom = null;
  if (S.roomId !== id){
    if (S.unsub) S.unsub();
    S.roomId = id; S.room = null;
    history.replaceState(null, '', '?r=' + id);
    S.unsub = S.db.on(`rooms/${id}`, onRoom);
  }
  S.joined = true;
  if (!S.presenceSet){
    S.presenceSet = true;
    S.db.presence(`rooms/${id}/players/${S.pid}`, () => S.joined && S.roomId === id);
  }
  render();
}

async function leave(){
  if (!confirm('部屋を出ますか？')) return;
  const id = S.roomId, path = `rooms/${id}/players/${S.pid}`;
  S.joined = false;
  if (S.unsub){ S.unsub(); S.unsub = null; }
  try {
    S.db.cancelPresence(path);
    const others = onlinePlayers().filter(p => p.id !== S.pid);
    if (others.length === 0) await S.db.set(`rooms/${id}`, null);
    else await S.db.set(path, null);
  } catch(e){}
  pidStore.set(id, null);
  location.href = baseUrl();
}

function onRoom(room){
  if (!room){
    if (S.roomId && S.joined) toast('部屋がなくなりました');
    if (S.unsub){ S.unsub(); S.unsub = null; }
    S.roomId = null; S.room = null; S.joined = false;
    history.replaceState(null, '', baseUrl());
    render(); return;
  }
  const prev = S.room;
  S.room = room;
  effects(prev);
  hostMigration();
  actorProcess();
  render();
}

// ホストがいなくなったら、いちばん先に入った人がホストになる
function hostMigration(){
  const m = me(); if (!m || !m.online) return;
  const h = P()[R().meta && R().meta.hostId];
  if (h && h.name && h.online) return;
  const first = onlinePlayers()[0];
  if (first && first.id === S.pid) upd({ 'meta/hostId':S.pid });
}

// 音や演出（状態の変化を見て鳴らす）
function effects(prev){
  const g = G(), pg = prev && prev.game ? prev.game : {};
  const logs = vals(R().log);
  const okCount = logs.filter(x => x.type === 'correct').length;
  const passCount = logs.filter(x => x.type === 'pass').length;
  const key = `${g.seed}:${g.turn}`;
  const [pk, pok, ppass] = (S.prevLogKey || '::').split('|');
  if (pk === key){
    if (okCount > Number(pok || 0)){ beep('ok'); popEmoji('🎉'); if (navigator.vibrate) navigator.vibrate(60); }
    else if (passCount > Number(ppass || 0)) beep('pass');
  }
  S.prevLogKey = `${key}|${okCount}|${passCount}`;
  if (g.phase !== pg.phase){
    if (g.phase === 'turnEnd') beep('end');
    if (g.phase === 'final') beep('win');
  }
}

// ===================== ゲームの進行 =====================
function startError(){
  const s = settings(), ps = onlinePlayers();
  if (!GENRES.some(x => s.genres && s.genres[x.id])) return 'ジャンルを1つ以上えらんでね';
  if (s.battle === 'solo') return ps.length < 2 ? '2人以上で遊べます' : '';
  const r = ps.filter(p => p.team === 'red').length, b = ps.filter(p => p.team === 'blue').length;
  if (r < 2 || b < 2) return 'チーム戦は、それぞれのチームに2人以上必要です';
  return '';
}
function buildOrder(ps, c){
  const order = [];
  if (c.battle === 'solo'){
    for (let r = 0; r < c.turnsEach; r++) ps.forEach(p => order.push(p.id));
  } else {
    const red = ps.filter(p => p.team === 'red'), blue = ps.filter(p => p.team === 'blue');
    const n = c.turnsEach * Math.max(red.length, blue.length);
    for (let k = 0; k < n; k++){ order.push(red[k % red.length].id); order.push(blue[k % blue.length].id); }
  }
  return order;
}
function startGame(){
  if (!isHost() || startError()) return;
  const c = JSON.parse(JSON.stringify(settings()));
  c.limitSec = clampLimit(c.limitSec);
  const ps = onlinePlayers();
  const order = buildOrder(ps, c);
  const game = { phase:'ready', cfg:c, order, turn:0, actorId:order[0], correct:0, pass:0,
    wordNo:0, deckPos:0, seed:(Math.random() * 2147483647) | 0, teamScores:{ red:0, blue:0 } };
  if (c.battle === 'team') game.actorTeam = P()[order[0]].team;
  const u = { game, log:null, guesses:null };
  playerList().forEach(p => { u[`players/${p.id}/score`] = 0; });
  upd(u);
}
function actorStart(){
  const g = G(); if (g.phase !== 'ready' || g.actorId !== S.pid) return;
  S.processed.clear(); S.ending = null;
  const startAt = S.db.now() + 3500;
  upd({ 'game/phase':'playing', 'game/startAt':startAt,
    'game/endAt': g.cfg.timeMode === 'limit' ? startAt + g.cfg.limitSec * 1000 : null,
    'game/correct':0, 'game/pass':0, log:null, guesses:null });
}
function endTurnFields(g, correct, now){
  const c = g.cfg;
  let sec = Math.max(0, (now - g.startAt) / 1000);
  sec = Math.min(sec, c.timeMode === 'limit' ? c.limitSec : c.targetMax);
  return {
    'game/phase':'turnEnd',
    [`game/records/${g.turn}`]: { actorId:g.actorId, team:g.actorTeam || null, correct, pass:g.pass || 0,
      sec:Math.round(sec * 10) / 10, cleared: c.timeMode === 'target' ? correct >= c.target : false }
  };
}
function endTurn(){
  const g = G(); if (g.phase !== 'playing') return;
  const k = `${g.seed}:${g.turn}`; if (S.ending === k) return; S.ending = k;
  upd(endTurnFields(g, g.correct || 0, S.db.now()));
}
function markCorrect(by){
  const g = G(); if (g.phase !== 'playing' || g.actorId !== S.pid) return;
  const now = S.db.now(); if (now < g.startAt) return;
  const k = `${g.seed}:${g.wordNo}`; if (S.busyWord === k) return;
  const w = currentWord(); if (!w) return;
  S.busyWord = k;
  const c = g.cfg, ps = P(), correct = (g.correct || 0) + 1;
  const u = { 'game/correct':correct, 'game/wordNo':(g.wordNo || 0) + 1, 'game/deckPos':(g.deckPos || 0) + 1 };
  u[`log/${newKey()}`] = { type:'correct', word:w.display, by:by || null, byName: by && ps[by] ? ps[by].name : null, t:now };
  if (by && ps[by]) u[`players/${by}/score`] = (ps[by].score || 0) + 1;
  if (ps[S.pid]) u[`players/${S.pid}/score`] = (ps[S.pid].score || 0) + 1;
  if (c.battle === 'team'){ const tm = g.actorTeam; u[`game/teamScores/${tm}`] = ((g.teamScores || {})[tm] || 0) + 1; }
  if (c.timeMode === 'target' && correct >= c.target){
    Object.assign(u, endTurnFields(g, correct, now)); S.ending = `${g.seed}:${g.turn}`;
  }
  upd(u);
}
function doPass(){
  const g = G(); if (g.phase !== 'playing' || g.actorId !== S.pid) return;
  const now = S.db.now(); if (now < g.startAt) return;
  const k = `${g.seed}:${g.wordNo}`; if (S.busyWord === k) return; S.busyWord = k;
  const w = currentWord();
  upd({ 'game/pass':(g.pass || 0) + 1, 'game/wordNo':(g.wordNo || 0) + 1, 'game/deckPos':(g.deckPos || 0) + 1,
    [`log/${newKey()}`]:{ type:'pass', word:w ? w.display : '', t:now } });
}
function nextTurn(){
  const g = G();
  if (!(isHost() || g.actorId === S.pid)) return;
  if (!['ready', 'turnEnd'].includes(g.phase)) return;
  const t = (g.turn || 0) + 1;
  const base = { log:null, guesses:null, 'game/deckPos':(g.deckPos || 0) + 1, 'game/wordNo':(g.wordNo || 0) + 1 };
  if (t >= (g.order || []).length){ upd({ ...base, 'game/phase':'final' }); return; }
  const aid = g.order[t];
  upd({ ...base, 'game/phase':'ready', 'game/turn':t, 'game/actorId':aid,
    'game/actorTeam': g.cfg.battle === 'team' ? ((P()[aid] || {}).team || null) : null,
    'game/correct':0, 'game/pass':0, 'game/startAt':null, 'game/endAt':null });
}
function playAgain(){
  if (!isHost()) return;
  const u = { game:{ phase:'lobby' }, log:null, guesses:null };
  playerList().forEach(p => { u[`players/${p.id}`] = p.online ? { ...strip(p), score:0 } : null; });
  upd(u);
}
const strip = p => { const { id, ...rest } = p; return rest; };

// 演じる人の端末：入力された答えを判定する
function actorProcess(){
  const g = G();
  if (g.phase !== 'playing' || g.actorId !== S.pid || !g.cfg || g.cfg.answer === 'voice') return;
  if (S.busyWord === `${g.seed}:${g.wordNo}`) return;
  const w = currentWord(); if (!w) return;
  const gs = Object.entries(R().guesses || {}).filter(([, x]) => x).sort((a, b) => (a[1].t || 0) - (b[1].t || 0));
  for (const [k, x] of gs){
    if (S.processed.has(k)) continue;
    S.processed.add(k);
    if (x.wordNo !== g.wordNo || !canGuess(x.pid)) continue;
    if (judge(x.text, w)){ markCorrect(x.pid); break; }
  }
}

// 0.1秒ごと：タイマー表示・カウントダウン・時間切れチェック
function tick(){
  const cd = document.getElementById('countdown');
  if (!S.room){ cd.hidden = true; return; }
  const g = G(), now = S.db.now();
  if (g.phase === 'playing' && g.cfg){
    const c = g.cfg, pre = now < g.startAt;
    if (pre){
      const n = Math.ceil((g.startAt - now) / 1000);
      cd.hidden = false;
      if (S.lastCount !== n){ S.lastCount = n; cd.innerHTML = `<span>${n}</span>`; beep('tick'); }
    } else if (S.lastCount && S.lastCount > 0){
      S.lastCount = 0; cd.innerHTML = '<span class="go">スタート！</span>'; beep('go');
      setTimeout(() => { if (S.lastCount === 0) cd.hidden = true; }, 700);
    } else if (S.lastCount === null){ cd.hidden = true; }

    const tEl = document.getElementById('timerNum');
    if (tEl){
      let txt, warn = false;
      if (c.timeMode === 'limit'){
        const rem = pre ? c.limitSec : Math.max(0, Math.ceil((g.endAt - now) / 1000));
        txt = fmtClock(rem); warn = !pre && rem <= 5;
        if (warn && rem > 0 && S.lastWarn !== rem){ S.lastWarn = rem; beep('warn'); }
      } else {
        const el = pre ? 0 : Math.min((now - g.startAt) / 1000, c.targetMax);
        txt = fmtSec(el); warn = !pre && c.targetMax - el <= 10;
      }
      tEl.textContent = txt;
      tEl.parentElement.classList.toggle('warn', warn);
    }
    const wc = document.querySelector('.word-card');
    if (wc) wc.classList.toggle('hide', pre);

    if (!pre){
      const over = c.timeMode === 'limit' ? now >= g.endAt : now - g.startAt >= c.targetMax * 1000;
      if (g.actorId === S.pid && over) endTurn();
      // 演じる人の通信が切れても止まらないように、ホストが少し待ってから終了させる
      if (isHost() && g.actorId !== S.pid){
        const late = c.timeMode === 'limit' ? now >= g.endAt + 3000 : now - g.startAt >= c.targetMax * 1000 + 3000;
        if (late) endTurn();
      }
    }
  } else {
    if (!cd.hidden && S.lastCount !== 0) cd.hidden = true;
    S.lastCount = null; S.lastWarn = null;
    if (g.phase === 'ready' && isHost() && g.order && !(P()[g.actorId] && P()[g.actorId].name)){
      const k = 'skip:' + g.seed + ':' + g.turn;
      if (S.ending !== k){ S.ending = k; nextTurn(); }
    }
  }
}

// ===================== 画面 =====================
function screenKey(){
  if (!S.roomId) return S.pendingRoom ? 'join' : 'home';
  if (!S.room) return 'loading';
  if (!me()) return 'join';
  const g = G();
  switch (g.phase){
    case 'ready': return 'ready';
    case 'playing': return g.actorId === S.pid ? 'play-actor' : (canGuess(S.pid) ? 'play-guess' : 'play-watch');
    case 'turnEnd': return 'turnEnd';
    case 'final': return 'final';
    default: return 'lobby';
  }
}

function render(){
  const key = screenKey();
  if (key !== S.screenKey){
    S.screenKey = key;
    document.body.dataset.screen = key;
    app.innerHTML = skeleton(key);
    window.scrollTo(0, 0);
    const inp = document.getElementById('guessInput');
    if (inp && !matchMedia('(pointer:coarse)').matches) inp.focus();
  }
  fill(key);
}
function setHTML(id, html){
  const el = document.getElementById(id);
  if (el && el._h !== html){ el._h = html; el.innerHTML = html; }
}

const topbar = () => `<div class="topbar"><div class="room-tag">部屋 <b>${esc(S.roomId)}</b></div>
  <div><button class="icon-btn" data-action="sound" id="soundBtn">${S.sound ? '🔊' : '🔇'}</button><button class="icon-btn" data-action="leave">退出</button></div></div>`;
const localBanner = () => S.local ? `<div class="banner">🧪 <b>デモモード</b>：Firebaseが未設定なので、<b>同じブラウザの別タブ同士</b>でだけ遊べます。READMEの手順で設定すると、みんなのスマホで遊べます。</div>` : '';
const nameForm = (btnLabel) => `<form id="nameForm" autocomplete="off">
  <label for="nameInput">なまえ</label>
  <input type="text" id="nameInput" maxlength="10" placeholder="例：たろう" value="${esc(store.get('gesture-name') || '')}">
  <button class="btn big primary" type="submit">${btnLabel}</button></form>`;

function skeleton(key){
  switch (key){
    case 'home': return `
      <div class="hero"><div class="logo">${rainbow('ジェスチャー\nパーティー')}</div><p>体だけで伝えて、みんなで当てよう！</p></div>
      ${localBanner()}
      <div class="card">${nameForm('部屋をつくる')}</div>
      <div class="card howto"><h3>あそびかた</h3><ol>
        <li>部屋をつくって、URLをみんなに送る</li>
        <li>演じる人のスマホにだけお題が出る</li>
        <li>声を出さずにジェスチャーで伝える！</li>
        <li>ほかの人は答えを入力するか、声で答える</li></ol></div>`;
    case 'join': return `
      <div class="hero"><div class="logo sm">${rainbow('ジェスチャー\nパーティー')}</div></div>
      ${localBanner()}
      <div class="card"><h2>部屋 <span style="letter-spacing:.1em">${esc(S.pendingRoom || S.roomId)}</span> にさんか</h2>${nameForm('入る')}
      <button class="link-btn" type="button" data-action="home">新しく部屋をつくる</button></div>`;
    case 'loading': return `<div class="loading">つないでいます…</div>`;
    case 'lobby': return `${topbar()}${two(`
      <div class="card"><div class="small" style="text-align:center">この部屋のURLをみんなに送ってね</div>
        <div class="code">${esc(S.roomId)}</div>
        <div class="share"><button class="btn yellow" data-action="copy">URLコピー</button><button class="btn yellow" data-action="share">送る</button><button class="btn yellow" data-action="qr">QR</button></div>
        <div id="qr" class="qr" hidden></div></div>
      <div class="card"><h2>あそぶ人 <span id="pcount" class="small"></span></h2><div id="players"></div></div>
      <div id="startArea" class="sticky-start"></div>`, `
      <div class="card"><h2>ルール <span id="hostNote" class="small"></span></h2><div id="settings"></div></div>`, 'lobby')}`;
    case 'ready': return `${topbar()}${two(`
      <div class="center-stage"><div class="small" id="turnNo"></div><div id="readyInfo"></div></div>
      <div id="readyAction"></div>`, `
      <div class="card"><h3>スコア</h3><div id="scoreboard"></div></div>`, 'ready')}`;
    case 'play-actor': return `${topbar()}${two(`
      ${playHead()}
      <div class="word-card hide"><div class="word-genre" id="wordGenre"></div><div class="word" id="word"></div>
        <div class="word-hint">声を出さずに体で表現しよう！</div><div class="word-wait">じゅんび…</div></div>`, `
      <div class="actor-btns" id="actorButtons"></div>
      <div class="card feed-card"><h3>みんなの回答</h3><div class="feed" id="feed"></div></div>`, 'play')}`;
    case 'play-guess':
    case 'play-watch': {
      const c = G().cfg || DEFAULT_SETTINGS;
      let input = '';
      if (key === 'play-watch') input = `<div class="note">👀 相手チームの番です。<br>見て楽しもう！（答えは言わないでね）</div>`;
      else if (c.answer === 'voice') input = `<div class="note">🗣️ 声で答えよう！<br>正解すると演じる人がボタンをおします</div>`;
      else input = `<form id="guessForm" class="guess-form" autocomplete="off"><input type="text" id="guessInput" maxlength="30" placeholder="答えを入力" enterkeyhint="send"><button class="btn primary" type="submit">送信</button></form>
        ${c.answer === 'both' ? '<div class="small" style="text-align:center;margin:-6px 0 12px">声で答えてもOK！</div>' : ''}`;
      return `${topbar()}${two(`
      ${playHead()}
      <div class="actor-banner" id="actorBanner"></div>
      ${input}`, `
      <div class="card feed-card"><h3>回答</h3><div class="feed" id="feed"></div></div>
      <div id="hostTools"></div>`, 'play')}`;
    }
    case 'turnEnd': return `${topbar()}${two(`
      <div class="center-stage" id="turnResultHead"></div>
      <div class="card"><h3>このターンのお題</h3><div id="turnWords"></div></div>`, `
      <div class="card"><h3>スコア</h3><div id="scoreboard"></div></div>
      <div id="nextArea"></div>`, 'turnend')}`;
    case 'final': return `${topbar()}
      <div class="center-stage"><div class="final-title">🏆 けっかはっぴょう 🏆</div></div>
      <div id="finalArea" class="final-grid"></div><div id="finalActions" class="final-actions"></div>`;
  }
  return '';
}
// 2列レイアウト（スマホ縦では上下に並び、タブレットや横向きでは左右に並ぶ）
const two = (a, b, cls) => `<div class="layout layout-${cls}"><div class="col col-a">${a}</div><div class="col col-b">${b}</div></div>`;
const playHead = () => `<div class="play-head"><div class="timer"><span id="timerNum">-</span><small id="timerUnit"></small></div><div class="counter" id="counter"></div></div>`;

function fill(key){
  const g = G(), c = g.cfg || settings();
  switch (key){
    case 'lobby': {
      const s = settings(), host = isHost();
      setHTML('pcount', `${onlinePlayers().length}/${MAX_PLAYERS}人`);
      setHTML('players', playersHTML(s));
      setHTML('hostNote', host ? '（あなたがホストです👑）' : '（ホストが決めます）');
      setHTML('settings', settingsHTML(s, host));
      const err = startError();
      setHTML('startArea', host
        ? `<button class="btn huge primary" data-action="start" ${err ? 'disabled' : ''}>ゲームスタート！</button>${err ? `<p class="small" style="text-align:center">${err}</p>` : ''}`
        : `<div class="note">ホスト（👑）がスタートするのを待っています…</div>`);
      break;
    }
    case 'ready': {
      const a = g.actorId, actorHere = !!(P()[a] && P()[a].name), actorOn = actorHere && P()[a].online;
      setHTML('turnNo', `ターン ${(g.turn || 0) + 1} / ${(g.order || []).length}`);
      setHTML('readyInfo', `<div class="big-emoji">${pEmoji(a)}</div><div class="turn-name">${esc(pName(a))} さんの番！</div>
        ${c.battle === 'team' ? teamBadge(g.actorTeam) : ''}<div class="rule-text">${ruleText(c)}</div>`);
      if (a === S.pid){
        setHTML('readyAction', `<div class="note">🤫 お題はあなたの画面にだけ出ます。<br>まわりの人に見えないようにしてね！</div>
          <button class="btn huge primary" data-action="actorStart">スタート！</button>`);
      } else {
        setHTML('readyAction', `<div class="note">${esc(pName(a))} さんがスタートするのを待っています…${!actorOn ? '<br><span class="small">（通信が切れているようです）</span>' : ''}</div>
          ${isHost() ? '<button class="btn" data-action="skip">この番をとばす</button>' : ''}`);
      }
      setHTML('scoreboard', scoreboardHTML());
      break;
    }
    case 'play-actor': {
      fillCounter(g, c);
      const w = currentWord();
      const wEl = document.getElementById('word');
      if (w && wEl && wEl.textContent !== w.display){
        wEl.textContent = w.display;
        document.getElementById('wordGenre').textContent = `${w.icon} ${w.genre}`;
        const card = document.querySelector('.word-card');
        card.classList.remove('new'); void card.offsetWidth; card.classList.add('new');
      }
      setHTML('actorButtons', actorButtonsHTML(g, c));
      setHTML('feed', feedHTML(true));
      break;
    }
    case 'play-guess':
    case 'play-watch': {
      fillCounter(g, c);
      setHTML('actorBanner', `${pEmoji(g.actorId)} <b>${esc(pName(g.actorId))}</b> さんが演じています ${c.battle === 'team' ? teamBadge(g.actorTeam) : ''}`);
      setHTML('feed', feedHTML(false));
      const a = P()[g.actorId];
      setHTML('hostTools', isHost() && !(a && a.online) ? `<button class="btn" data-action="forceEnd">この番を終わる（演じる人の通信が切れています）</button>` : '');
      break;
    }
    case 'turnEnd': {
      const rec = (g.records || {})[g.turn] || {};
      let head;
      if (c.timeMode === 'limit') head = `<div class="result-head">⏰ タイムアップ！</div><div class="result-sub">${esc(pName(g.actorId))} さん：<b>${rec.correct || 0}問</b> 正解</div>`;
      else if (rec.cleared) head = `<div class="result-head">🎊 クリア！</div><div class="result-sub">${esc(pName(g.actorId))} さん：<b>${fmtSec(rec.sec)}秒</b></div>`;
      else head = `<div class="result-head">⏰ 時間切れ…</div><div class="result-sub">${esc(pName(g.actorId))} さん：${rec.correct || 0} / ${c.target}問</div>`;
      setHTML('turnResultHead', head);
      setHTML('turnWords', turnWordsHTML(g, c, rec));
      setHTML('scoreboard', scoreboardHTML());
      const last = (g.turn || 0) + 1 >= (g.order || []).length;
      const canNext = isHost() || g.actorId === S.pid;
      setHTML('nextArea', canNext
        ? `<button class="btn big primary" data-action="next">${last ? '結果を見る 🏆' : '次の人へ ▶'}</button>`
        : `<div class="note">次へ進むのを待っています…</div>`);
      break;
    }
    case 'final': {
      setHTML('finalArea', finalHTML(g, c));
      setHTML('finalActions', (isHost() ? `<button class="btn big primary" data-action="again">もう一度あそぶ</button>` : `<div class="note">ホストが「もう一度あそぶ」をおすと、ロビーにもどります</div>`)
        + `<button class="btn" data-action="leave">部屋を出る</button>`);
      break;
    }
  }
}

// 制限時間のプルダウン
function onChange(e){
  const el = e.target; if (!el.dataset || !el.dataset.tpart || !isHost()) return;
  const box = el.closest('.time-pick');
  const m = Number(box.querySelector('[data-tpart=m]').value);
  const s = m === 10 ? 0 : Number(box.querySelector('[data-tpart=s]').value);
  upd({ 'settings/limitSec': clampLimit(m * 60 + s) });
}

function fillCounter(g, c){
  setHTML('counter', c.timeMode === 'limit'
    ? `<span>正解</span><b>${g.correct || 0}</b><span>パス ${g.pass || 0}</span>`
    : `<span>正解</span><b>${g.correct || 0}/${c.target}</b><span>パス ${g.pass || 0}</span>`);
  setHTML('timerUnit', c.timeMode === 'limit' ? 'のこり時間' : `秒（最大${c.targetMax}秒）`);
}
const teamBadge = t => t ? `<span class="badge ${t}">${TEAM[t].name}</span>` : '';
const ruleText = c => c.timeMode === 'limit' ? `${fmtJa(c.limitSec)}で何問当ててもらえるかな？` : `${c.target}問当ててもらうまでのタイムは？`;

function chipHTML(p, clickable){
  const host = R().meta && R().meta.hostId === p.id;
  const cls = `pchip ${p.online ? '' : 'off'} ${p.id === S.pid ? 'me' : ''}`;
  const inner = `${p.emoji || '🙂'} ${esc(p.name)}${host ? ' 👑' : ''}`;
  return clickable ? `<button class="${cls}" data-action="team" data-id="${p.id}" title="タップでチームをかえる">${inner}</button>` : `<span class="${cls}">${inner}</span>`;
}
function playersHTML(s){
  const ps = playerList();
  if (s.battle === 'solo') return `<div class="players">${ps.map(p => chipHTML(p, false)).join('')}</div>`;
  const col = t => `<div class="team-col ${t}"><h4>${TEAM[t].name}</h4><div class="players">${
    ps.filter(p => p.team === t).map(p => chipHTML(p, isHost() || p.id === S.pid)).join('') || '<span class="small">だれもいません</span>'}</div></div>`;
  return `<div class="team-cols">${col('red')}${col('blue')}</div>
    <p class="small" style="margin:10px 0 0">名前をタップするとチームをかえられます${isHost() ? '' : '（自分のみ）'}</p>
    ${isHost() ? '<button class="btn yellow" style="margin-top:10px" data-action="shuffleTeams">ランダムに分ける 🎲</button>' : ''}`;
}
function settingsHTML(s, editable){
  let h = '';
  for (const row of SETTING_ROWS){
    if (row.show && !row.show(s)) continue;
    if (row.time){
      const v = clampLimit(s[row.key]), m = Math.floor(v / 60), sec = v % 60, dis = editable ? '' : 'disabled';
      const mOpts = Array.from({ length:10 }, (_, i) => i + 1).map(x => `<option value="${x}" ${x === m ? 'selected' : ''}>${x}</option>`).join('');
      const sOpts = [0, 10, 20, 30, 40, 50].map(x => `<option value="${x}" ${x === sec ? 'selected' : ''}>${String(x).padStart(2, '0')}</option>`).join('');
      h += `<div class="set-row"><div class="set-label">${row.label}</div><div class="time-pick">
        <select data-tpart="m" aria-label="分" ${dis}>${mOpts}</select><span>分</span>
        <select data-tpart="s" aria-label="秒" ${dis || (m === 10 ? 'disabled' : '')}>${sOpts}</select><span>秒</span></div>
        <div class="seg-help">1分〜10分のあいだで、10秒ごとに決められます</div></div>`;
      continue;
    }
    h += `<div class="set-row"><div class="set-label">${row.label}</div><div class="seg">${
      row.opts.map(([v, l]) => `<button data-action="set" data-key="${row.key}" data-val="${v}" class="${s[row.key] === v ? 'on' : ''}" ${editable ? '' : 'disabled'}>${l}</button>`).join('')
    }</div>${row.help ? `<div class="seg-help">${row.help(s)}</div>` : ''}</div>`;
  }
  h += `<div class="set-row"><div class="set-label">お題のジャンル</div><div class="seg">${
    GENRES.map(x => `<button data-action="genre" data-id="${x.id}" class="${s.genres && s.genres[x.id] ? 'on' : ''}" ${editable ? '' : 'disabled'}>${x.icon} ${x.name}</button>`).join('')
  }</div></div>`;
  return h;
}
function actorButtonsHTML(g, c){
  let h = '';
  if (c.answer !== 'type'){
    if (c.battle === 'solo'){
      const gs = playerList().filter(p => canGuess(p.id));
      h += `<p class="who-label">✅ 正解！当てた人をタップ</p><div class="who-grid">${
        gs.map(p => `<button class="btn green" data-action="correct" data-id="${p.id}">${p.emoji || ''} ${esc(p.name)}</button>`).join('')}</div>`;
    } else {
      h += `<button class="btn huge green" data-action="correct">⭕ 正解！</button>`;
    }
  } else {
    h += `<div class="note">みんなが入力した答えを自動で判定します</div>`;
  }
  h += `<button class="btn" data-action="pass">パス ⏭</button>`;
  return h;
}
function feedHTML(forActor){
  const items = [];
  for (const x of vals(R().guesses)) items.push({ t:x.t || 0, html:`<div class="fi">${esc(x.emoji || '')} <b>${esc(x.name)}</b>：${esc(x.text)}</div>` });
  for (const x of vals(R().log)){
    if (x.type === 'correct') items.push({ t:(x.t || 0) + 1, html:`<div class="fi ok">🎉 ${x.byName ? `<b>${esc(x.byName)}</b> さん ` : ''}正解！「${esc(x.word)}」</div>` });
    else items.push({ t:x.t || 0, html:`<div class="fi pass">⏭ パス${forActor ? `（${esc(x.word)}）` : ''}</div>` });
  }
  items.sort((a, b) => b.t - a.t);
  return items.length ? items.slice(0, 20).map(i => i.html).join('') : '<div class="empty">まだ回答はありません</div>';
}
function turnWordsHTML(g, c, rec){
  const logs = vals(R().log).sort((a, b) => (a.t || 0) - (b.t || 0));
  let h = '<ul class="wl">';
  for (const x of logs){
    if (x.type === 'correct') h += `<li class="ok"><span>✅ ${esc(x.word)}</span><span>${x.byName ? esc(x.byName) + ' さん' : ''}</span></li>`;
    else h += `<li class="pass"><span>⏭ ${esc(x.word)}</span><span>パス</span></li>`;
  }
  if (!rec.cleared){
    const w = currentWord();
    if (w) h += `<li class="left"><span>⌛ ${esc(w.display)}</span><span>時間切れ</span></li>`;
  }
  h += '</ul>';
  return logs.length || !rec.cleared ? h : '<div class="empty">お題はありませんでした</div>';
}
function teamTotals(g){
  const t = { red:{ score:0, sec:0, turns:0, cleared:0 }, blue:{ score:0, sec:0, turns:0, cleared:0 } };
  for (const k of ['red', 'blue']) t[k].score = (g.teamScores || {})[k] || 0;
  for (const r of vals(g.records)){
    if (!t[r.team]) continue;
    t[r.team].sec += r.sec || 0; t[r.team].turns++; if (r.cleared) t[r.team].cleared++;
  }
  return t;
}
function teamWinner(g, c){
  const t = teamTotals(g);
  if (c.timeMode === 'limit') return t.red.score === t.blue.score ? null : (t.red.score > t.blue.score ? 'red' : 'blue');
  if (Math.abs(t.red.sec - t.blue.sec) < 0.05) return t.red.score === t.blue.score ? null : (t.red.score > t.blue.score ? 'red' : 'blue');
  return t.red.sec < t.blue.sec ? 'red' : 'blue';
}
function vsHTML(g, c, showWin){
  const t = teamTotals(g), win = showWin ? teamWinner(g, c) : null;
  const box = k => `<div class="team-score ${k} ${win === k ? 'win' : ''}">${win === k ? '<div class="crown">👑</div>' : ''}<div>${TEAM[k].name}</div>${
    c.timeMode === 'limit' ? `<div class="num">${t[k].score}</div><div>問</div>` : `<div class="num">${fmtSec(t[k].sec)}</div><div>秒（${t[k].turns}回）</div>`}</div>`;
  return `<div class="vs">${box('red')}<div class="vs-mid">VS</div>${box('blue')}</div>
    ${c.timeMode === 'target' ? '<p class="small" style="text-align:center;margin:10px 0 0">タイムの合計が少ないほうが勝ち！</p>' : ''}
    ${showWin && !win ? '<p style="text-align:center;font-weight:800;font-size:20px">ひきわけ！</p>' : ''}`;
}
function rankHTML(list, scoreFn){
  let prev = null, pos = 0;
  return list.map((p, i) => {
    const sc = scoreFn(p);
    if (sc !== prev){ pos = i + 1; prev = sc; }
    const medal = ['🥇','🥈','🥉'][pos - 1] || pos;
    return `<div class="rank ${pos === 1 ? 'first' : ''}"><span class="pos">${medal}</span><span class="nm">${p.emoji || ''} ${esc(p.name)}</span><span class="sc">${sc}</span></div>`;
  }).join('');
}
function scoreboardHTML(){
  const g = G(), c = g.cfg || settings();
  if (c.battle === 'team') return vsHTML(g, c, false);
  const ps = playerList().sort((a, b) => (b.score || 0) - (a.score || 0));
  return rankHTML(ps, p => `${p.score || 0}<small>点</small>`);
}
function finalHTML(g, c){
  let h = '';
  const ps = playerList().sort((a, b) => (b.score || 0) - (a.score || 0));
  if (c.battle === 'team') h += `<div class="card">${vsHTML(g, c, true)}</div>`;
  h += `<div class="card"><div class="section-title">${c.battle === 'team' ? '⭐ がんばった人' : '⭐ 個人ランキング'}</div>${rankHTML(ps, p => `${p.score || 0}<small>点</small>`)}
    <p class="small" style="margin:8px 0 0">演じて当ててもらうと1点、当てると1点</p></div>`;
  const recs = vals(g.records).map(r => ({ ...r, name:pName(r.actorId), emoji:pEmoji(r.actorId) }));
  if (recs.length){
    if (c.timeMode === 'target'){
      recs.sort((a, b) => (b.cleared - a.cleared) || (a.cleared ? a.sec - b.sec : b.correct - a.correct));
      h += `<div class="card"><div class="section-title">⏱ タイムランキング（${c.target}問）</div>${
        rankHTML(recs, r => r.cleared ? `${fmtSec(r.sec)}<small>秒</small>` : `${r.correct}<small>問</small>`)}</div>`;
    } else {
      recs.sort((a, b) => b.correct - a.correct);
      h += `<div class="card"><div class="section-title">🎭 演技ランキング（${fmtJa(c.limitSec)}）</div>${
        rankHTML(recs, r => `${r.correct}<small>問</small>`)}</div>`;
    }
  }
  return h;
}

// ===================== 操作 =====================
async function onClick(e){
  unlockAudio();
  const el = e.target.closest('[data-action]'); if (!el) return;
  const a = el.dataset.action;
  switch (a){
    case 'home': location.href = baseUrl(); break;
    case 'copy': copyUrl(); break;
    case 'share': shareUrl(); break;
    case 'qr': toggleQr(); break;
    case 'sound':
      S.sound = !S.sound; store.set('gesture-sound', S.sound ? 'on' : 'off');
      el.textContent = S.sound ? '🔊' : '🔇'; if (S.sound) beep('tick'); break;
    case 'leave': leave(); break;
    case 'set': {
      if (!isHost()) return;
      const row = SETTING_ROWS.find(r => r.key === el.dataset.key); if (!row) return;
      const v = typeof row.opts[0][0] === 'number' ? Number(el.dataset.val) : el.dataset.val;
      upd({ [`settings/${row.key}`]:v }); break;
    }
    case 'genre': {
      if (!isHost()) return;
      const s = settings(), id = el.dataset.id, on = !(s.genres && s.genres[id]);
      const count = GENRES.filter(x => s.genres && s.genres[x.id]).length;
      if (!on && count <= 1){ toast('ジャンルは1つ以上えらんでね'); return; }
      upd({ [`settings/genres/${id}`]:on }); break;
    }
    case 'team': {
      const id = el.dataset.id; if (!(isHost() || id === S.pid) || G().phase !== 'lobby') return;
      const p = P()[id]; if (!p) return;
      upd({ [`players/${id}/team`]: p.team === 'red' ? 'blue' : 'red' }); break;
    }
    case 'shuffleTeams': {
      if (!isHost()) return;
      const u = {}; shuffle(onlinePlayers()).forEach((p, i) => { u[`players/${p.id}/team`] = i % 2 ? 'blue' : 'red'; });
      upd(u); break;
    }
    case 'start': startGame(); break;
    case 'actorStart': actorStart(); break;
    case 'correct': markCorrect(el.dataset.id || null); break;
    case 'pass': doPass(); break;
    case 'skip': nextTurn(); break;
    case 'forceEnd': endTurn(); break;
    case 'next': nextTurn(); break;
    case 'again': playAgain(); break;
  }
}

async function onSubmit(e){
  if (e.target.id === 'nameForm'){
    e.preventDefault(); unlockAudio();
    const name = document.getElementById('nameInput').value.trim().slice(0, 10);
    if (!name){ toast('なまえを入れてね'); return; }
    store.set('gesture-name', name);
    if (S.busy) return; S.busy = true;
    const target = S.pendingRoom || (S.roomId && !me() ? S.roomId : null);
    try { if (target) await joinRoom(target, name); else await createRoom(name); }
    catch(err){ console.error(err); toast('つながりませんでした。もう一度ためしてね'); }
    finally { S.busy = false; }
  }
  if (e.target.id === 'guessForm'){
    e.preventDefault();
    const inp = document.getElementById('guessInput');
    const text = inp.value.trim().slice(0, 30); if (!text) return;
    const g = G(); if (g.phase !== 'playing' || !canGuess(S.pid)) return;
    if (S.db.now() < g.startAt){ toast('スタートまで待ってね'); return; }
    const m = me();
    upd({ [`guesses/${newKey()}`]:{ pid:S.pid, name:m.name, emoji:m.emoji || '', text, wordNo:g.wordNo || 0, t:S.db.now() } });
    inp.value = ''; inp.focus();
  }
}

async function copyUrl(){
  try { await navigator.clipboard.writeText(roomUrl()); toast('URLをコピーしました'); }
  catch(e){ prompt('このURLを送ってね', roomUrl()); }
}
async function shareUrl(){
  if (navigator.share){
    try { await navigator.share({ title:'ジェスチャーパーティー', text:'ジェスチャーゲームしよう！', url:roomUrl() }); } catch(e){}
  } else copyUrl();
}
function toggleQr(){
  const box = document.getElementById('qr'); if (!box) return;
  if (!box.hidden){ box.hidden = true; return; }
  box.hidden = false;
  const draw = () => { box.innerHTML = ''; new QRCode(box, { text:roomUrl(), width:180, height:180 }); };
  if (window.QRCode) return draw();
  box.textContent = 'よみこみ中…';
  const s = document.createElement('script');
  s.src = 'https://cdnjs.cloudflare.com/ajax/libs/qrcodejs/1.0.0/qrcode.min.js';
  s.onload = draw; s.onerror = () => { box.textContent = 'QRコードを表示できませんでした'; };
  document.head.appendChild(s);
}

// ===================== スタート =====================
async function main(){
  S.sound = store.get('gesture-sound') !== 'off';
  document.addEventListener('click', onClick);
  document.addEventListener('submit', onSubmit);
  document.addEventListener('change', onChange);
  await initDB();
  setInterval(tick, 100);
  const r = (new URLSearchParams(location.search).get('r') || '').toUpperCase().replace(/[^A-Z0-9]/g, '');
  if (r){
    S.pendingRoom = r;
    const pid = pidStore.get(r), name = store.get('gesture-name');
    if (pid && name){
      render();
      try { await joinRoom(r, name); return; } catch(e){ console.error(e); }
    }
  }
  render();
}
main();
})();
