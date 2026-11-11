'use strict';
/* Moteur de jeu : simulation + rendu du vol. */

const ENEMY_TYPES = {
  gnat:    { sprite: 'gnat',    hp: 3,   spd: 74, dmg: 4,  rew: 0.6, ai: 'chase', dieOnHit: true },
  scout:   { sprite: 'scout',   hp: 7,   spd: 50, dmg: 6,  rew: 1,   ai: 'chase' },
  weaver:  { sprite: 'weaver',  hp: 11,  spd: 46, dmg: 7,  rew: 1.5, ai: 'weave' },
  shooter: { sprite: 'shooter', hp: 18,  spd: 34, dmg: 6,  rew: 2.5, ai: 'shoot' },
  kami:    { sprite: 'kami',    hp: 12,  spd: 34, dmg: 14, rew: 2,   ai: 'charge', dieOnHit: true },
  tank:    { sprite: 'tank',    hp: 75,  spd: 21, dmg: 14, rew: 6,   ai: 'chase' },
  hive:    { sprite: 'hive',    hp: 130, spd: 14, dmg: 10, rew: 9,   ai: 'hive', noRot: true },
  cargo:   { sprite: 'cargo',   hp: 55,  spd: 44, dmg: 0,  rew: 28,  ai: 'flee' },
};

const BOSSES = [
  { sprite: 'boss1', name: 'SENTINELLE', ai: 'spiral' },
  { sprite: 'boss2', name: 'MÈRE-RUCHE', ai: 'brood' },
  { sprite: 'boss3', name: 'TITAN',      ai: 'ram' },
  { sprite: 'boss4', name: 'ŒIL DU VIDE', ai: 'blink' },
];

const NEBULA_PAL = [
  ['#090b20', '#0d1030'],
  ['#0f0920', '#160c30'],
  ['#14081a', '#1d0b24'],
  ['#07141b', '#0a1c26'],
];

const BOSS_BUFF_SECTOR = 5;  // à partir d'ici : 3 fois plus de vie, attaques 2 fois plus rapides
const BOSS_BUFF_HP = 3;
const BOSS_BUFF_ATTACK = 2;
const TWO_BOSS_SECTOR = 10;  // à partir d'ici : deux boss en même temps

const Game = (() => {
  let cv, ctx;
  let VW = 640, VH = 360, pixelScale = 3;

  let p = null;
  let run = null;
  let enemies = [], pBullets = [], eBullets = [], missiles = [], mines = [], orbs = [];
  let parts = [], rings = [], novas = [], bolts = [], texts = [], droneList = [];
  let bosses = [];        // un boss, puis deux à partir de TWO_BOSS_SECTOR
  let time = 0, shake = 0, frameT = 0, accumulator = 0;
  let camX = 0, camY = 0;

  /* Plusieurs vaisseaux peuvent voler ensemble. p, ST et droneList désignent toujours
     celui qui agit à cet instant : le reste du moteur n'a pas à savoir lequel c'est. */
  let players = [];
  let me = null;          // le vaisseau de ce joueur (celui que suit la caméra)
  let ST = null;
  let mode = 'solo';      // solo | host | guest
  let viewW = 640, viewH = 360;
  let nextNid = 1;

  function setActor(ship) { p = ship; ST = ship.st; droneList = ship.drones; }
  const ownerOf = o => players[o] || me;
  function nearestAlive(x, y) {
    let best = null, bd = Infinity;
    for (const s of players) {
      if (s.dead) continue;
      const d = (s.x - x) * (s.x - x) + (s.y - y) * (s.y - y);
      if (d < bd) { bd = d; best = s; }
    }
    return best || players[0];
  }
  function randomAlive() {
    const list = players.filter(s => !s.dead);
    return list.length ? pick(list) : players[0];
  }
  const inCoop = () => players.length > 1;
  const RESCUE_BASE = 3;      // secondes pour la première réparation d'un allié
  const RESCUE_RADIUS = 70;   // distance à laquelle il faut rester

  /* Ce que l'hôte fait voir et entendre à l'invité. */
  const NOT_FORWARDED = new Set(['shoot', 'hit', 'hurt', 'shieldHit', 'dash', 'buy', 'deny', 'click']);
  function sfx(name) {
    Audio8.fx[name]();
    if (mode === 'host' && !NOT_FORWARDED.has(name)) Coop.queue(['s', name]);
  }
  function sayToast(text) { UI.toast(text); if (mode === 'host') Coop.queue(['T', text]); }
  function sayBanner(a, b, c) { UI.banner(a, b, c); if (mode === 'host') Coop.queue(['B', a, b || '', !!c]); }
  /* Change de morceau ici et chez l'invité. */
  function sayMusic(kind, sector) {
    if (kind === 'stop') Music.stop(); else Music[kind](sector);
    if (mode === 'host') Coop.queue(['m', kind, sector || 1]);
  }

  const stars = [[], [], []];
  const nebulae = [];

  /* ---------- Grille spatiale ---------- */
  const CELL = 40, BUCKETS = 1024;
  const grid = Array.from({ length: BUCKETS }, () => []);
  let qid = 0;
  const hashCell = (cx, cy) => (((cx * 73856093) ^ (cy * 19349663)) >>> 0) % BUCKETS;

  function rebuildGrid() {
    for (let i = 0; i < BUCKETS; i++) grid[i].length = 0;
    for (const e of enemies) {
      if (e.dead) continue;
      grid[hashCell(Math.floor(e.x / CELL), Math.floor(e.y / CELL))].push(e);
      if (e.r > CELL / 2) { // grands sprites : présents dans plusieurs cellules
        const x0 = Math.floor((e.x - e.r) / CELL), x1 = Math.floor((e.x + e.r) / CELL);
        const y0 = Math.floor((e.y - e.r) / CELL), y1 = Math.floor((e.y + e.r) / CELL);
        for (let cx = x0; cx <= x1; cx++) for (let cy = y0; cy <= y1; cy++) {
          const b = grid[hashCell(cx, cy)];
          if (!b.includes(e)) b.push(e);
        }
      }
    }
  }
  function near(x, y, r, fn) {
    const id = ++qid;
    const x0 = Math.floor((x - r) / CELL), x1 = Math.floor((x + r) / CELL);
    const y0 = Math.floor((y - r) / CELL), y1 = Math.floor((y + r) / CELL);
    for (let cx = x0; cx <= x1; cx++) {
      for (let cy = y0; cy <= y1; cy++) {
        const b = grid[hashCell(cx, cy)];
        for (let i = 0; i < b.length; i++) {
          const e = b[i];
          if (e.q === id || e.dead) continue;
          e.q = id;
          const dx = e.x - x, dy = e.y - y, rr = r + e.r;
          if (dx * dx + dy * dy <= rr * rr) { if (fn(e) === false) return; }
        }
      }
    }
  }
  function nearest(x, y, maxD, exclude) {
    let best = null, bd = maxD * maxD;
    for (const e of enemies) {
      if (e.dead || (exclude && exclude.has(e))) continue;
      const dx = e.x - x, dy = e.y - y, d = dx * dx + dy * dy;
      if (d < bd) { bd = d; best = e; }
    }
    return best;
  }

  /* ---------- Entrées ---------- */
  const Input = {
    keys: {}, mx: 0, my: 0, mouseSeen: false, dashQueued: false,
    stick: null, // { id, ox, oy, x, y }
  };
  function moveVector() {
    let x = 0, y = 0;
    const k = Input.keys;
    if (k.KeyA || k.ArrowLeft) x -= 1;
    if (k.KeyD || k.ArrowRight) x += 1;
    if (k.KeyW || k.ArrowUp) y -= 1;
    if (k.KeyS || k.ArrowDown) y += 1;
    if (Input.stick) {
      const dx = Input.stick.x - Input.stick.ox, dy = Input.stick.y - Input.stick.oy;
      const d = Math.hypot(dx, dy);
      if (d > 4) { const m = Math.min(1, d / 40); x = (dx / d) * m; y = (dy / d) * m; }
    }
    const l = Math.hypot(x, y);
    if (l > 1) { x /= l; y /= l; }
    return { x, y };
  }

  /* ---------- Démarrage ---------- */
  function init(canvas) {
    cv = canvas;
    ctx = cv.getContext('2d');
    resize();
    window.addEventListener('resize', resize);
    for (let l = 0; l < 3; l++) {
      for (let i = 0; i < 90; i++) stars[l].push({ x: rnd(1024), y: rnd(1024), tw: rnd(TAU) });
    }
    buildNebulae();
    bindInput();
  }

  function resize() {
    // Fenêtre réduite ou masquée : taille nulle, on garde la vue précédente.
    if (window.innerWidth < 2 || window.innerHeight < 2) return;
    const dpr = window.devicePixelRatio || 1;
    const physW = window.innerWidth * dpr;
    const physH = window.innerHeight * dpr;
    // En portrait, on zoome davantage : sinon le vaisseau devient minuscule sur téléphone.
    const target = physH > physW * 1.2 ? 300 : 340;
    pixelScale = Math.max(1, Math.round(Math.min(physW, physH) / target));
    VW = Math.ceil(physW / pixelScale);
    VH = Math.ceil(physH / pixelScale);
    cv.width = VW;
    cv.height = VH;
    ctx.imageSmoothingEnabled = false;
    if (typeof Coop !== 'undefined') { updateView(); Coop.sendView(); }
  }

  /* Nébuleuses pré-calculées, tramées à l'ancienne et raccordables. */
  function buildNebulae() {
    const SIZE = 320, LAT = 8;
    const bayer = [0, 8, 2, 10, 12, 4, 14, 6, 3, 11, 1, 9, 15, 7, 13, 5];
    for (const pal of NEBULA_PAL) {
      const lat = [];
      for (let i = 0; i < LAT * LAT; i++) lat.push(Math.random());
      const lat2 = [];
      const L2 = LAT * 2;
      for (let i = 0; i < L2 * L2; i++) lat2.push(Math.random());
      const sample = (g, L, x, y) => {
        const fx = (x / SIZE) * L, fy = (y / SIZE) * L;
        const ix = Math.floor(fx), iy = Math.floor(fy);
        const tx = fx - ix, ty = fy - iy;
        const sx = tx * tx * (3 - 2 * tx), sy = ty * ty * (3 - 2 * ty);
        const v = (a, b) => g[((b % L) * L) + (a % L)];
        const a = v(ix, iy) * (1 - sx) + v(ix + 1, iy) * sx;
        const b = v(ix, iy + 1) * (1 - sx) + v(ix + 1, iy + 1) * sx;
        return a * (1 - sy) + b * sy;
      };
      const c = document.createElement('canvas');
      c.width = c.height = SIZE;
      const x2 = c.getContext('2d');
      for (let y = 0; y < SIZE; y++) {
        for (let x = 0; x < SIZE; x++) {
          const n = sample(lat, LAT, x, y) * 0.68 + sample(lat2, L2, x, y) * 0.32;
          const dth = bayer[(y % 4) * 4 + (x % 4)] / 16;
          const lvl = (n - 0.42) * 3.4 + (dth - 0.5) * 0.5;
          if (lvl > 0.72) { x2.fillStyle = pal[1]; x2.fillRect(x, y, 1, 1); }
          else if (lvl > 0.22) { x2.fillStyle = pal[0]; x2.fillRect(x, y, 1, 1); }
        }
      }
      nebulae.push(c);
    }
  }

  function makeShip(st, idx, remote) {
    return {
      idx, remote, st, drones: [], patches: [], beam: null,
      x: idx * 34, y: 0, vx: 0, vy: 0, ang: -Math.PI / 2, aim: -Math.PI / 2,
      hull: st.maxHull, shield: st.shield ? st.maxHull * st.shieldMul : 0,
      shieldT: 0, invuln: 1, flash: 0,
      fireT: 0, missileT: 1, mineT: 1, arcT: 0.5, novaT: 2, beamT: 0, trailT: 0,
      dashT: 0, dashCd: 0, charges: st.dashCharges, dashVX: 0, dashVY: 0, dashHit: null, netDash: false,
      revives: st.revive, frenzy: 0, frenzyT: 0, collectT: 0,
      dead: false, thrust: 0, maxHullSeen: st.maxHull, rescue: 0, rescues: 0, rescueNeed: RESCUE_BASE,
      netAim: null, fired: false, award: { u: 0, c: 0 },
    };
  }

  function clearWorld() {
    enemies = []; pBullets = []; eBullets = []; missiles = []; mines = []; orbs = [];
    parts = []; rings = []; novas = []; bolts = []; texts = [];
    bosses = [];
    accumulator = 0;
    shake = 0;
  }

  function updateView() {
    const mate = Coop.mate();
    viewW = Math.max(VW, mate ? mate.vw : 0);
    viewH = Math.max(VH, mate ? mate.vh : 0);
  }

  function start(sector) {
    computeStats();
    const mate = Coop.mate();
    mode = mate ? 'host' : 'solo';
    players = [makeShip(STATS, 0, false)];
    if (mate) players.push(makeShip(mate.st, 1, true));
    me = players[0];
    clearWorld();
    updateView();
    for (const s of players) { setActor(s); syncDrones(); }
    setActor(me);
    run = {
      sector, startSector: sector, t: 0, time: 0, dur: STATS.sectorDur,
      spawnAcc: 0, ringT: 14, cargoT: rnd(18, 28) / STATS.cargoMul,
      kills: 0, units: 0, cores: 0, bossesKilled: 0,
      combo: 0, comboT: 0, bestCombo: 0, over: false, deathT: 0,
    };
    if (S.best < sector) S.best = sector;
    S.runs++;
    sayMusic('flight', sector);
    sayBanner('SECTEUR ' + sector, mate ? 'Tous les ennemis convergent vers vous' : 'Tous les ennemis convergent vers toi');
  }

  /* L'invité ne simule que son propre pilotage : tout le reste vient de l'hôte. */
  function startGuest(msg) {
    computeStats();
    mode = 'guest';
    const host = makeShip(msg.st, 0, true);
    me = makeShip(STATS, 1, false);
    players = [host, me];
    clearWorld();
    updateView();
    for (const s of players) { setActor(s); syncDrones(); }
    setActor(me);
    run = {
      sector: msg.sector, startSector: msg.sector, t: 0, time: 0, dur: 60,
      kills: 0, units: 0, cores: 0, bossesKilled: 0, combo: 0, bestCombo: 0, over: false,
    };
    // L'hôte peut faire partir l'invité plus loin que son record : le record affiché suit aussi.
    noteSectorReached(msg.sector);
    S.runs++;
    Music.flight(msg.sector);
    UI.banner('SECTEUR ' + msg.sector, 'Tous les ennemis convergent vers vous');
  }

  function syncDrones() {
    const n = ST.drones;
    while (droneList.length < n) {
      droneList.push({ x: p ? p.x : 0, y: p ? p.y : 0, fireT: rnd(1), arcT: rnd(3), ramT: 0, offset: 0 });
    }
    droneList.length = n;
    droneList.forEach((d, i) => { d.offset = (i / Math.max(1, n)) * TAU; });
  }

  function applyStats(ship, st) {
    const prevMax = ship.maxHullSeen || st.maxHull;
    ship.st = st;
    setActor(ship);
    syncDrones();
    // Une amélioration de coque achetée en vol profite tout de suite : on garde le même pourcentage.
    if (mode !== 'guest') {
      ship.hull = Math.min(st.maxHull, (ship.hull / prevMax) * st.maxHull);
      if (!st.shield) ship.shield = 0;
    }
    ship.maxHullSeen = st.maxHull;
    setActor(me);
  }

  /* Rappelé quand un achat change les statistiques pendant un vol. */
  function onStatsChanged() {
    Coop.sendStats();
    if (!me) return;
    applyStats(me, STATS);
  }

  /* L'autre joueur vient d'améliorer son vaisseau. */
  function setMateStats(st) {
    if (!me) return;
    const mate = players.find(s => s !== me);
    if (mate) applyStats(mate, st);
    updateView();
  }

  /* L'invité est parti : l'hôte continue seul. */
  function removeMate() {
    if (mode !== 'host') return;
    players = [me];
    mode = 'solo';
    updateView();
    setActor(me);
  }

  /* ---------- Échelles par secteur ---------- */
  const hpMul = s => Math.pow(1.32, s - 1);
  const rewMul = s => Math.pow(1.16, s - 1);
  const dmgMul = s => Math.pow(1.2, s - 1);

  /* ---------- Apparitions ---------- */
  function spawnPos(margin = 24) {
    const hw = viewW / 2 + margin, hh = viewH / 2 + margin;
    const side = Math.random() < 0.5 ? -1 : 1;
    if (Math.random() < hw / (hw + hh)) return { x: p.x + rnd(-hw, hw), y: p.y + side * hh };
    return { x: p.x + side * hw, y: p.y + rnd(-hh, hh) };
  }

  function spawnEnemy(typeName, pos, opts = {}) {
    const t = ENEMY_TYPES[typeName];
    const spr = Sprites[t.sprite].n;
    const at = pos || spawnPos();
    const s = run.sector;
    const ramp = 1 + 0.25 * clamp(run.t / run.dur, 0, 1.5);
    const elite = opts.noElite ? false : Math.random() < ST.eliteC && s >= 2 && typeName !== 'cargo';
    const hp = t.hp * hpMul(s) * ramp * (elite ? 5 : 1) * (inCoop() ? 1.25 : 1);
    const e = {
      nid: nextNid++ & 0xffff, type: typeName, t, x: at.x, y: at.y, vx: 0, vy: 0,
      hp, maxHp: hp,
      r: Math.max(3, Math.min(spr.width, spr.height) * 0.42),
      spd: t.spd * Math.min(2.4, 1 + 0.03 * (s - 1)) * rnd(0.92, 1.08),
      dmg: t.dmg * dmgMul(s) * (elite ? 1.5 : 1),
      rew: t.rew * rewMul(s) * (elite ? 6 : 1),
      elite, boss: false, flash: 0, ang: 0, timer: rnd(1), state: 0, wob: rnd(TAU),
      slow: 0, slowT: 0, q: 0, dead: false, drawScale: 1, life: 0,
    };
    enemies.push(e);
    return e;
  }

  function spawnTable(s) {
    const out = [['gnat', 5], ['scout', 5]];
    if (s >= 2) out.push(['weaver', 3]);
    if (s >= 3) out.push(['shooter', 2.5 + s * 0.25]);
    if (s >= 4) out.push(['kami', 2.5]);
    if (s >= 5) out.push(['tank', 1.6]);
    if (s >= 6) out.push(['hive', 0.6]);
    return out;
  }

  function pickSpawn(s) {
    const table = spawnTable(s);
    let total = 0;
    for (const row of table) total += row[1];
    let v = rnd(total);
    for (const row of table) { v -= row[1]; if (v <= 0) return row[0]; }
    return 'scout';
  }

  function updateSpawns(dt) {
    setActor(randomAlive());
    const st = ST, s = run.sector;
    const prog = clamp(run.t / run.dur, 0, 1.5);
    let rate = (0.9 + 0.14 * (s - 1)) * (1 + 0.8 * prog) * st.spawnMul;
    // Boss présent : répit au début, puis la pression monte si on traîne.
    if (bosses.length) rate *= Math.min(1.25, 0.4 + 0.01 * Math.max(0, run.t - run.dur));
    if (inCoop()) rate *= 1.5;
    rate = Math.min(rate, 9 * st.spawnMul * (inCoop() ? 1.5 : 1));
    run.spawnAcc += rate * dt;
    while (run.spawnAcc >= 1) {
      run.spawnAcc -= 1;
      if (enemies.length >= 240) continue;
      const type = pickSpawn(s);
      if (type === 'gnat') {
        const at = spawnPos();
        const n = rndi(3, 5);
        for (let i = 0; i < n; i++) spawnEnemy('gnat', { x: at.x + rnd(-14, 14), y: at.y + rnd(-14, 14) });
      } else spawnEnemy(type);
    }
    // Encerclement : un anneau complet, pour que ça vienne vraiment de partout.
    run.ringT -= dt;
    if (run.ringT <= 0 && enemies.length < 200) {
      run.ringT = Math.max(8, 22 - s * 0.8);
      const n = Math.min(60, 12 + s * 3);
      const R = Math.hypot(viewW, viewH) / 2 + 20;
      const type = s >= 7 && Math.random() < 0.4 ? 'scout' : 'gnat';
      for (let i = 0; i < n; i++) {
        const a = (i / n) * TAU;
        spawnEnemy(type, { x: p.x + Math.cos(a) * R, y: p.y + Math.sin(a) * R }, { noElite: true });
      }
    }
    // Cargos pleins d'unités qui tentent de s'enfuir.
    run.cargoT -= dt;
    if (run.cargoT <= 0) {
      run.cargoT = rnd(26, 40) / st.cargoMul;
      spawnEnemy('cargo');
      sayToast('CARGO REPÉRÉ — détruis-le avant qu\'il ne fuie !');
    }
    // Le boss.
    if (!bosses.length && run.t >= run.dur) spawnBosses();
  }

  function spawnBosses() {
    const s = run.sector;
    const buffed = s >= BOSS_BUFF_SECTOR;
    const count = s >= TWO_BOSS_SECTOR ? 2 : 1;
    const hp = 300 * Math.pow(1.42, s - 1) * (inCoop() ? 1.7 : 1) * (buffed ? BOSS_BUFF_HP : 1);
    for (let i = 0; i < count; i++) {
      // Deux boss différents : chacun attaque à sa façon.
      const bossIdx = (s - 1 + i) % BOSSES.length;
      const def = BOSSES[bossIdx];
      const spr = Sprites[def.sprite].n;
      const at = spawnPos(50);
      const boss = {
        nid: nextNid++ & 0xffff, bossIdx,
        type: 'boss', t: { sprite: def.sprite, ai: def.ai, noRot: true, dmg: 0 }, def,
        x: at.x, y: at.y, vx: 0, vy: 0, hp, maxHp: hp,
        r: Math.min(spr.width, spr.height) * 0.9,
        spd: 34, dmg: 16 * dmgMul(s), rew: 60 * rewMul(s),
        attackRate: buffed ? BOSS_BUFF_ATTACK : 1,
        elite: false, boss: true, flash: 0, ang: 0, timer: 1.5, timer2: 0, spin: 0, state: 0, wob: 0,
        slow: 0, slowT: 0, q: 0, dead: false, drawScale: 2, life: 0, tx: 0, ty: 0,
      };
      bosses.push(boss);
      enemies.push(boss);
    }
    sfx('alarm');
    sayMusic('boss', s);
    sayBanner('ALERTE', bosses.map(b => b.def.name).join(' et ') + ' — secteur ' + s, true);
    shake = Math.max(shake, 5);
  }

  function nearestBoss(x, y) {
    let best = null, bd = Infinity;
    for (const b of bosses) {
      if (b.dead) continue;
      const d = (b.x - x) * (b.x - x) + (b.y - y) * (b.y - y);
      if (d < bd) { bd = d; best = b; }
    }
    return best;
  }

  /* ---------- Tirs ennemis ---------- */
  function fireEnemy(x, y, ang, speed, dmg, color = '#ff5a8a', r = 2) {
    if (eBullets.length > 400) return;
    const sp = speed * Math.min(1.7, 1 + 0.02 * (run.sector - 1));
    eBullets.push({ x, y, vx: Math.cos(ang) * sp, vy: Math.sin(ang) * sp, dmg, life: 6, r, color });
  }

  /* ---------- IA ---------- */
  function updateEnemy(e, dt) {
    e.life += dt;
    if (e.flash > 0) e.flash -= dt;
    if (e.slowT > 0) e.slowT -= dt; else e.slow = 0;
    const dx = p.x - e.x, dy = p.y - e.y;
    const dist = Math.hypot(dx, dy) || 1;
    const nx = dx / dist, ny = dy / dist;

    // On ne sème pas un boss : il accélère avec le temps et revient au contact.
    if (e.boss) {
      const late = Math.max(0, run.t - run.dur - 20);
      e.spd = 34 * Math.min(3, 1 + late * 0.02);
      if (dist > Math.hypot(viewW, viewH) * 0.85) {
        const at = spawnPos(20);
        e.x = at.x; e.y = at.y;
      }
    }

    let slowF = 1 - e.slow;
    if (ST.slowAura > 0 && dist < 110) slowF *= 1 - ST.slowAura;
    let spd = e.spd * slowF;
    let tvx = nx * spd, tvy = ny * spd;

    switch (e.t.ai) {
      case 'weave': {
        const w = Math.sin(e.life * 3.2 + e.wob) * 1.1;
        tvx = (nx - ny * w) * spd;
        tvy = (ny + nx * w) * spd;
        break;
      }
      case 'shoot': {
        const want = 120;
        const k = dist > want + 15 ? 1 : dist < want - 15 ? -0.8 : 0;
        const orbit = Math.sin(e.wob) > 0 ? 0.5 : -0.5;
        tvx = (nx * k - ny * orbit) * spd;
        tvy = (ny * k + nx * orbit) * spd;
        e.timer -= dt;
        if (e.timer <= 0 && dist < 230) {
          e.timer = rnd(2, 2.8);
          fireEnemy(e.x, e.y, Math.atan2(dy, dx), 96, e.dmg, '#ffb24a');
        }
        break;
      }
      case 'charge': {
        if (e.state === 0) { // approche
          if (dist < 125) { e.state = 1; e.timer = 0.55; }
        } else if (e.state === 1) { // préparation : s'immobilise et clignote
          tvx = 0; tvy = 0;
          e.timer -= dt;
          e.ang = Math.atan2(dy, dx) + Math.PI / 2;
          if (Math.floor(e.timer * 18) % 2 === 0) e.flash = 0.03;
          if (e.timer <= 0) { e.state = 2; e.timer = 0.9; e.cx = nx; e.cy = ny; }
        } else { // charge
          tvx = e.cx * 230 * slowF;
          tvy = e.cy * 230 * slowF;
          e.timer -= dt;
          if (Math.random() < 0.5) spark(e.x, e.y, '#ffe14a');
          if (e.timer <= 0) { e.state = 0; }
        }
        break;
      }
      case 'hive': {
        e.timer -= dt;
        if (e.timer <= 0 && enemies.length < 230) {
          e.timer = 3.6;
          for (let i = 0; i < 3; i++) {
            const a = rnd(TAU);
            spawnEnemy('gnat', { x: e.x + Math.cos(a) * e.r, y: e.y + Math.sin(a) * e.r }, { noElite: true });
          }
        }
        break;
      }
      case 'flee': {
        tvx = -nx * spd * (dist < 170 ? 1.15 : 0.7);
        tvy = -ny * spd * (dist < 170 ? 1.15 : 0.7);
        e.timer += dt;
        if (e.life > 26) { e.dead = true; e.escaped = true; sayToast('Le cargo a pris la fuite.'); }
        break;
      }
      case 'spiral': bossSpiral(e, dt, nx, ny, dist); return;
      case 'brood': bossBrood(e, dt, nx, ny, dist); return;
      case 'ram': bossRam(e, dt, nx, ny, dist); return;
      case 'blink': bossBlink(e, dt, nx, ny, dist); return;
    }

    // Ralentissement du recul : la vitesse courante rejoint la vitesse voulue.
    const blend = Math.min(1, dt * 5);
    e.vx += (tvx - e.vx) * blend;
    e.vy += (tvy - e.vy) * blend;
    e.x += e.vx * dt;
    e.y += e.vy * dt;
    if (!e.t.noRot && e.state !== 1 && (e.vx || e.vy)) e.ang = Math.atan2(e.vy, e.vx) + Math.PI / 2;

    // Trop loin : on le ramène en bordure d'écran.
    if (dist > Math.hypot(viewW, viewH) * 1.15 && e.t.ai !== 'flee') {
      const at = spawnPos();
      e.x = at.x; e.y = at.y;
    }
  }

  function bossMove(e, dt, nx, ny, dist, want, speed) {
    const k = dist > want + 12 ? 1 : dist < want - 12 ? -0.6 : 0;
    e.vx += (nx * k * speed - e.vx) * Math.min(1, dt * 2);
    e.vy += (ny * k * speed - e.vy) * Math.min(1, dt * 2);
    e.x += e.vx * dt;
    e.y += e.vy * dt;
  }
  const bossExtra = () => Math.floor(run.sector / 5);

  function bossSpiral(e, dt, nx, ny, dist) {
    bossMove(e, dt, nx, ny, dist, 120, e.spd);
    e.spin += dt * 1.5;
    const attack = dt * e.attackRate;
    e.timer -= attack;
    if (e.timer <= 0) {
      e.timer = 0.2;
      const arms = 2 + bossExtra();
      for (let i = 0; i < arms; i++) {
        fireEnemy(e.x, e.y, e.spin + (i / arms) * TAU, 84, e.dmg * 0.6, '#ff5a8a', 2);
      }
    }
    e.timer2 -= attack;
    if (e.timer2 <= 0) {
      e.timer2 = 4.5;
      const a = Math.atan2(ny, nx);
      for (let i = -2; i <= 2; i++) fireEnemy(e.x, e.y, a + i * 0.16, 120, e.dmg * 0.8, '#ffe14a', 3);
    }
  }
  function bossBrood(e, dt, nx, ny, dist) {
    bossMove(e, dt, nx, ny, dist, 150, e.spd * 0.8);
    const attack = dt * e.attackRate;
    e.timer -= attack;
    if (e.timer <= 0 && enemies.length < 230) {
      e.timer = 2.8;
      for (let i = 0; i < 5 + bossExtra(); i++) {
        const a = rnd(TAU);
        spawnEnemy(i % 3 === 2 ? 'scout' : 'gnat', { x: e.x + Math.cos(a) * e.r, y: e.y + Math.sin(a) * e.r }, { noElite: true });
      }
    }
    e.timer2 -= attack;
    if (e.timer2 <= 0) {
      e.timer2 = 1.7;
      const a = Math.atan2(ny, nx);
      const n = 1 + bossExtra();
      for (let i = -n; i <= n; i++) fireEnemy(e.x, e.y, a + i * 0.22, 110, e.dmg * 0.7, '#6cf06c', 3);
    }
  }
  function bossRam(e, dt, nx, ny, dist) {
    // La charge garde sa longueur : c'est l'attente entre deux charges qui raccourcit.
    e.timer -= e.state === 2 ? dt : dt * e.attackRate;
    if (e.state === 0) {            // traque
      bossMove(e, dt, nx, ny, dist, 60, e.spd * 1.1);
      if (e.timer <= 0) { e.state = 1; e.timer = 0.9; e.cx = nx; e.cy = ny; }
    } else if (e.state === 1) {     // annonce : la trajectoire s'affiche
      e.cx = nx; e.cy = ny;
      e.vx *= 0.9; e.vy *= 0.9;
      if (e.timer <= 0) { e.state = 2; e.timer = 0.75; shake = Math.max(shake, 3); sfx('dash'); }
    } else if (e.state === 2) {     // charge
      e.x += e.cx * 330 * dt;
      e.y += e.cy * 330 * dt;
      if (Math.random() < 0.7) spark(e.x, e.y, '#ff9d2e');
      if (e.timer <= 0) {
        e.state = 0;
        e.timer = rnd(1.8, 2.6);
        const n = 12 + bossExtra() * 3;
        for (let i = 0; i < n; i++) fireEnemy(e.x, e.y, (i / n) * TAU, 96, e.dmg * 0.6, '#ff9d2e', 3);
        ringAt(e.x, e.y, 70, '#ff9d2e');
        shake = Math.max(shake, 4);
      }
    }
  }
  function bossBlink(e, dt, nx, ny, dist) {
    const attack = dt * e.attackRate;
    e.timer -= attack;
    e.spin += dt * 0.9;
    e.timer2 -= attack;
    if (e.timer2 <= 0) {
      e.timer2 = 0.14;
      const arms = 2 + bossExtra();
      for (let i = 0; i < arms; i++) fireEnemy(e.x, e.y, e.spin + (i / arms) * TAU, 110, e.dmg * 0.5, '#d86cff', 2);
    }
    if (e.timer <= 0) {
      e.timer = 4;
      burst(e.x, e.y, 26, ['#d86cff', '#ffffff'], 130, 0.5);
      const a = rnd(TAU);
      e.x = p.x + Math.cos(a) * 150;
      e.y = p.y + Math.sin(a) * 150;
      burst(e.x, e.y, 26, ['#d86cff', '#ffffff'], 130, 0.5);
      ringAt(e.x, e.y, 50, '#d86cff');
      const n = 14 + bossExtra() * 3;
      for (let i = 0; i < n; i++) fireEnemy(e.x, e.y, (i / n) * TAU, 80, e.dmg * 0.6, '#ff6cd0', 3);
    }
  }

  /* Empêche les ennemis de s'empiler sur le même pixel. */
  function separateEnemies(dt) {
    for (let i = 0; i < BUCKETS; i++) {
      const b = grid[i];
      if (b.length < 2) continue;
      for (let a = 0; a < b.length; a++) {
        const A = b[a];
        for (let c = a + 1; c < b.length && c < a + 7; c++) {
          const B = b[c];
          const dx = B.x - A.x, dy = B.y - A.y;
          const min = A.r + B.r;
          const d2 = dx * dx + dy * dy;
          if (d2 > 0.01 && d2 < min * min) {
            const d = Math.sqrt(d2);
            const push = ((min - d) / d) * dt * 8;
            if (!A.boss) { A.x -= dx * push; A.y -= dy * push; }
            if (!B.boss) { B.x += dx * push; B.y += dy * push; }
          }
        }
      }
    }
  }

  /* ---------- Dégâts infligés ---------- */
  function damageMultiplier() {
    let m = 1;
    if (ST.lastStand && p.hull < ST.maxHull * 0.25) m *= 1.5;
    if (ST.speedDmg > 0) m *= 1 + ST.speedDmg * (Math.hypot(p.vx, p.vy) / 50);
    return m;
  }

  function dealDamage(e, amount, o = {}) {
    if (e.dead) return;
    const st = ST;
    let dmg = amount * damageMultiplier();
    if (e.boss) dmg *= 1 + st.boss + st.elite * 0.5;
    if (e.elite) dmg *= 1 + st.elite;
    if (st.exec > 0 && e.hp < e.maxHp * 0.3) dmg *= 1 + st.exec;
    let crit = false;
    if (o.crit && Math.random() < st.critC) { dmg *= st.critM; crit = true; }
    e.hp -= dmg;
    e.flash = 0.07;
    if (o.slow > 0) { e.slow = Math.max(e.slow, o.slow); e.slowT = 1.2; }
    if (S.set.nums && texts.length < 60 && (!o.quiet || crit)) {
      const tx = e.x + rnd(-4, 4), ty = e.y - e.r, tc = crit ? 2 : o.color || 0, label = fmt(dmg);
      texts.push({ x: tx, y: ty, t: 0.55, s: label, c: tc });
      if (mode === 'host') Coop.queue(['x', Math.round(tx), Math.round(ty), label, tc]);
    }
    if (e.hp <= 0) killEnemy(e);
    else if (!o.quiet) sfx('hit');
  }

  function explosion(x, y, radius, dmg, color, o = {}) {
    near(x, y, radius, e => {
      dealDamage(e, dmg, { crit: !!o.crit, color: 5 });
      if (o.knock) {
        const d = Math.hypot(e.x - x, e.y - y) || 1;
        if (!e.boss) { e.vx += ((e.x - x) / d) * o.knock; e.vy += ((e.y - y) / d) * o.knock; }
      }
    });
    ringAt(x, y, radius, color);
    burst(x, y, Math.min(28, 6 + radius * 0.35), [color, '#ffffff', '#ff9d2e'], radius * 3, 0.35);
    sfx('boom');
    if (radius > 50) shake = Math.max(shake, 2);
  }

  function killEnemy(e) {
    e.dead = true;
    const st = ST;
    run.kills++;
    S.kills++;

    // Combo
    if (st.combo) {
      run.combo++;
      run.comboT = 2.5;
      if (run.combo > run.bestCombo) run.bestCombo = run.combo;
    }
    const comboBonus = st.combo ? Math.min(st.comboMax, run.combo * 0.01) : 0;

    // Frénésie
    if (st.frenzy) { p.frenzy = Math.min(st.frenzyMax, p.frenzy + 1); p.frenzyT = 2.5; }
    // Récupération
    if (st.repairKill > 0 && !p.dead) p.hull = Math.min(st.maxHull, p.hull + st.maxHull * st.repairKill);
    // Saut opportuniste
    if (st.dash && st.dashReset > 0 && (p.remote || p.charges < st.dashCharges) && Math.random() < st.dashReset) {
      if (p.remote) Coop.queue(['d']);
      else { p.charges++; p.dashCd = 0; }
    }

    // Récompense
    // Le multiplicateur de chaque joueur s'applique au ramassage : tout le monde profite de chaque orbe.
    let value = e.rew * (1 + comboBonus);
    if (e.elite || e.boss) value *= 1 + st.bounty;
    if (Math.random() < st.jackpot) {
      value *= st.jackpotMul;
      sayToast('JACKPOT !');
      ringAt(e.x, e.y, 34, '#ffd84a');
    }
    const pieces = e.boss ? 24 : e.type === 'cargo' ? 12 : e.elite ? 5 : value > 0 && e.r > 7 ? 3 : 1;
    for (let i = 0; i < pieces; i++) dropOrb(e.x, e.y, value / pieces, 'u', pieces > 1);

    if (e.elite && Math.random() < st.coreC) dropOrb(e.x, e.y, 1, 'c', true);
    if (e.type === 'cargo' && Math.random() < 0.35 + st.coreC) dropOrb(e.x, e.y, 1, 'c', true);

    // Effets
    const big = e.r > 7;
    burst(e.x, e.y, big ? 26 : 9, e.elite ? ['#ffd84a', '#fff6b0', '#ffffff'] : ['#ffffff', '#ff9d2e', '#ff4a4a'], big ? 110 : 70, big ? 0.55 : 0.32);
    if (big) { ringAt(e.x, e.y, e.r * 2.6, '#ff9d2e'); shake = Math.max(shake, 1.5); }
    sfx('kill');

    if (e.boss) onBossKilled(e);
  }

  function onBossKilled(e) {
    const st = ST;
    bosses = bosses.filter(b => b !== e);
    run.bossesKilled++;
    const coreN = Math.max(1, Math.round((1 + Math.floor(run.sector / 2) + st.coreBoss) * st.coreMul));
    const spread = Math.min(coreN, 8);
    for (let i = 0; i < spread; i++) {
      // Toujours des noyaux entiers : le reste de la division va aux premiers orbes.
      const share = Math.floor(coreN / spread) + (i < coreN % spread ? 1 : 0);
      dropOrb(e.x, e.y, share, 'c', true);
    }

    burst(e.x, e.y, 90, ['#ffffff', '#ffe14a', '#ff9d2e', '#ff4a4a'], 240, 1);
    for (let i = 0; i < 3; i++) ringAt(e.x + rnd(-20, 20), e.y + rnd(-20, 20), 70 + i * 40, '#ffe14a');
    shake = Math.max(shake, 8);
    if (mode === 'host') Coop.queue(['k', 8]);
    sfx('bigKill');
    if (bosses.length) {
      sayToast('Boss détruit : il en reste un !');
      return;
    }
    sfx('sector');

    // Secteur suivant
    run.sector++;
    run.t = 0;
    run.dur = st.sectorDur;
    sayMusic('flight', run.sector);
    if (noteSectorReached(run.sector)) sayToast(`POINT DE PASSAGE : secteur ${run.sector}`);
    if (mode === 'host') Coop.queue(['S', run.sector]);
    for (const s of players) {
      if (s.dead) reviveShip(s, 0.5); // le coéquipier tombé revient au secteur suivant
      else s.hull = Math.min(s.st.maxHull, s.hull + s.st.maxHull * 0.25);
    }
    eBullets.length = 0;
    const firstHyper = run.sector === HYPER_SECTOR && S.ascensions === 0;
    sayBanner('SECTEUR ' + run.sector, firstHyper ? 'HYPERSAUT DÉBLOQUÉ — voir la Constellation' : 'Boss vaincu : +' + fmt(coreN) + ' noyaux');
    Save.write();
  }

  /* ---------- Orbes ---------- */
  function dropOrb(x, y, val, kind, scatter) {
    if (orbs.length > 220 && kind === 'u') {
      // On fusionne plutôt que de saturer l'écran.
      const o = orbs[Math.floor(Math.random() * orbs.length)];
      if (o.kind === 'u') { o.val += val; return; }
    }
    const a = rnd(TAU), s = scatter ? rnd(30, 110) : rnd(0, 26);
    orbs.push({ x, y, vx: Math.cos(a) * s, vy: Math.sin(a) * s, val, kind, t: 0, pulled: false });
  }

  function collectOrb(o) {
    if (o.kind === 'u') {
      const v = o.val * me.st.gainMul;
      S.units += v;
      S.lifeUnits += v;
      S.ascUnits += v;
      run.units += v;
      for (const s of players) if (s.remote) s.award.u += o.val * s.st.gainMul;
      sfx('pickup');
    } else {
      const v = Math.round(o.val);
      S.cores += v;
      run.cores += v;
      for (const s of players) if (s.remote) s.award.c += v;
      sfx('core');
      sayToast('+' + fmt(v) + ' NOYAU' + (v >= 2 ? 'X' : ''));
    }
  }

  function updateOrbs(dt) {
    for (const s of players) {
      if (s.dead || !s.st.droneCollect) continue;
      s.collectT -= dt;
      if (s.collectT <= 0 && orbs.length) {
        s.collectT = 0.33;
        const o = orbs[Math.floor(Math.random() * orbs.length)];
        if (!o.pulled) {
          o.pulled = true;
          addBolt([s.x, s.y, o.x, o.y], 0.1, '#6cf06c');
        }
      }
    }
    const reach = Math.hypot(viewW, viewH) * 1.3;
    for (let i = orbs.length - 1; i >= 0; i--) {
      const o = orbs[i];
      o.t += dt;
      const ship = nearestAlive(o.x, o.y);
      const dx = ship.x - o.x, dy = ship.y - o.y;
      const d = Math.hypot(dx, dy) || 1;
      const onScreen = Math.abs(dx) < viewW / 2 + 20 && Math.abs(dy) < viewH / 2 + 20;
      if (o.t > 0.25 && (d < ship.st.magnet || o.pulled || (ship.st.vacuum && onScreen))) {
        const a = 900;
        o.vx += (dx / d) * a * dt;
        o.vy += (dy / d) * a * dt;
        const max = Math.max(260, Math.hypot(ship.vx, ship.vy) * 1.4);
        const sp = Math.hypot(o.vx, o.vy);
        if (sp > max) { o.vx *= max / sp; o.vy *= max / sp; }
      } else {
        o.vx *= 1 - Math.min(1, dt * 2.4);
        o.vy *= 1 - Math.min(1, dt * 2.4);
      }
      o.x += o.vx * dt;
      o.y += o.vy * dt;
      if (d < 9 && o.t > 0.1 && !ship.dead) {
        collectOrb(o);
        orbs[i] = orbs[orbs.length - 1];
        orbs.pop();
      } else if (d > reach) {
        // Trop loin derrière vous : rapatrié pour ne rien perdre.
        o.pulled = true;
      }
    }
  }

  /* ---------- Particules ---------- */
  function burst(x, y, n, colors, speed, life) {
    for (let i = 0; i < n && parts.length < 700; i++) {
      const a = rnd(TAU), s = rnd(speed * 0.2, speed);
      parts.push({ x, y, vx: Math.cos(a) * s, vy: Math.sin(a) * s, t: rnd(life * 0.5, life), c: pick(colors), z: Math.random() < 0.25 ? 2 : 1 });
    }
    if (mode === 'host') Coop.queue(['b', Math.round(x), Math.round(y), Math.round(n), colors, speed, life]);
  }
  function spark(x, y, c) {
    if (parts.length < 700) parts.push({ x, y, vx: rnd(-20, 20), vy: rnd(-20, 20), t: rnd(0.15, 0.3), c, z: 1 });
  }
  function ringAt(x, y, r, c) {
    if (rings.length < 40) rings.push({ x, y, r: r * 0.2, max: r, c, t: 0 });
    if (mode === 'host') Coop.queue(['r', Math.round(x), Math.round(y), Math.round(r), c]);
  }
  function addBolt(pts, t, color) {
    bolts.push({ pts, t, color });
    if (mode === 'host') Coop.queue(['l', pts.map(Math.round), t, color]);
  }

  /* ---------- Armes du joueur ---------- */
  function fireCannon(target) {
    const st = ST;
    const dmg = st.cannonDmg;
    const base = p.aim;
    const n = st.salvo;
    const sp = st.bulletSpeed;
    const spread = 0.13;
    for (let i = 0; i < n; i++) {
      const a = base + (i - (n - 1) / 2) * spread;
      addBullet(p.x + Math.cos(a) * 8, p.y + Math.sin(a) * 8, a, sp, dmg, target);
    }
    if (st.rear) addBullet(p.x, p.y, base + Math.PI, sp, dmg, null);
    if (st.side) {
      addBullet(p.x, p.y, base + 1.05, sp, dmg * 0.6, null);
      addBullet(p.x, p.y, base - 1.05, sp, dmg * 0.6, null);
    }
    if (p === me) sfx('shoot'); else p.fired = true;
    if (parts.length < 700) spark(p.x + Math.cos(base) * 9, p.y + Math.sin(base) * 9, '#ffffff');
  }
  function addBullet(x, y, a, sp, dmg, target, o = {}) {
    if (pBullets.length > 500) return;
    const st = ST;
    pBullets.push({
      o: p.idx, x, y, vx: Math.cos(a) * sp, vy: Math.sin(a) * sp, sp,
      dmg, life: (o.range || st.range) / sp,
      pierce: o.pierce === undefined ? st.pierce : o.pierce,
      bounce: o.bounce === undefined ? st.ricochet : o.bounce,
      crit: o.crit === undefined ? true : o.crit,
      target, hit: null, color: o.color || '#fff27a', shard: !!o.shard, drone: !!o.drone,
    });
  }

  function launchMissiles() {
    const st = ST;
    const count = st.missileN + (st.droneMissile ? droneList.length : 0);
    const nearbyCount = Math.min(enemies.length, 30);
    if (!nearbyCount) return false;
    let launched = 0;
    for (let i = 0; i < count; i++) {
      const a = p.aim + (i - (count - 1) / 2) * 0.5 + Math.PI + rnd(-0.1, 0.1);
      const src = i >= st.missileN && droneList[i - st.missileN] ? droneList[i - st.missileN] : p;
      missiles.push({
        x: src.x, y: src.y, vx: Math.cos(a) * 60, vy: Math.sin(a) * 60,
        o: p.idx, ang: a, target: bosses.length && i % 2 === 0 ? bosses[(i / 2) % bosses.length] : null, life: 3.2, trail: 0,
      });
      launched++;
    }
    if (launched) sfx('missile');
    return launched > 0;
  }

  function updateMissiles(dt) {
    for (let i = missiles.length - 1; i >= 0; i--) {
      const m = missiles[i];
      setActor(ownerOf(m.o));
      const st = ST;
      m.life -= dt;
      if (!m.target || m.target.dead) m.target = nearest(m.x, m.y, 320);
      if (m.target) {
        const want = Math.atan2(m.target.y - m.y, m.target.x - m.x);
        let d = want - m.ang;
        while (d > Math.PI) d -= TAU;
        while (d < -Math.PI) d += TAU;
        m.ang += clamp(d, -6 * dt, 6 * dt);
      }
      const sp = st.missileSpeed;
      m.vx += (Math.cos(m.ang) * sp - m.vx) * Math.min(1, dt * 5);
      m.vy += (Math.sin(m.ang) * sp - m.vy) * Math.min(1, dt * 5);
      m.x += m.vx * dt;
      m.y += m.vy * dt;
      m.trail -= dt;
      if (m.trail <= 0) { m.trail = 0.03; spark(m.x, m.y, Math.random() < 0.5 ? '#ff9d2e' : '#ffe14a'); }

      let hit = false;
      near(m.x, m.y, 4, () => { hit = true; return false; });
      if (hit || m.life <= 0) {
        detonateMissile(m);
        missiles[i] = missiles[missiles.length - 1];
        missiles.pop();
      }
    }
  }
  function detonateMissile(m) {
    const st = ST;
    let dmg = st.missileDmg;
    let rad = st.missileRad;
    let color = '#ff9d2e';
    if (Math.random() < st.nuke) {
      dmg *= 5; rad *= 2; color = '#ffffff';
      shake = Math.max(shake, 5);
    }
    explosion(m.x, m.y, rad, dmg, color, { crit: true });
    if (st.cluster > 0) {
      for (let k = 0; k < st.cluster; k++) {
        const a = (k / st.cluster) * TAU + rnd(0.3);
        addBullet(m.x, m.y, a, 260, dmg * 0.35, null, { range: 90, pierce: 0, bounce: 0, color: '#ffb24a', shard: true });
      }
    }
    if (st.plasma) fireArcFrom(m.x, m.y, 2, st.arc ? st.arcDmg : st.missileDmg * 0.5);
  }

  function fireArcFrom(x, y, chain, dmg) {
    const st = ST;
    const seen = new Set();
    let cx = x, cy = y;
    const pts = [cx, cy];
    let hits = 0;
    for (let i = 0; i <= chain; i++) {
      const e = nearest(cx, cy, i === 0 ? 150 : 95, seen);
      if (!e) break;
      seen.add(e);
      pts.push(e.x, e.y);
      dealDamage(e, dmg, { crit: true, slow: st.arcSlow, color: 4 });
      cx = e.x; cy = e.y;
      hits++;
    }
    if (hits) {
      addBolt(pts, 0.14, '#7ff0ff');
      sfx('arc');
    }
    return hits > 0;
  }

  function fireBeam(dt) {
    const st = ST;
    p.beamT -= dt;
    const target = nearest(p.x, p.y, st.beamLen + 10);
    p.beam = null;
    if (!target) return;
    const a = p.aim;
    const ca = Math.cos(a), sa = Math.sin(a);
    p.beam = { a, len: st.beamLen, w: st.beamW };
    if (p.beamT > 0) return;
    p.beamT = 0.1;
    const half = st.beamW / 2;
    for (const e of enemies) {
      if (e.dead) continue;
      const dx = e.x - p.x, dy = e.y - p.y;
      const along = dx * ca + dy * sa;
      if (along < 0 || along > st.beamLen + e.r) continue;
      const off = Math.abs(dx * -sa + dy * ca);
      if (off > e.r + half) continue;
      dealDamage(e, st.beamDps * 0.1, { crit: true, quiet: true });
      if (Math.random() < 0.3) spark(e.x, e.y, '#7ff0ff');
    }
  }

  function dropMines() {
    const st = ST;
    for (let i = 0; i < st.mineN; i++) {
      if (mines.length >= 40) mines.shift();
      const a = rnd(TAU), d = st.mineN > 1 ? rnd(4, 22) : 0;
      mines.push({ o: p.idx, x: p.x + Math.cos(a) * d, y: p.y + Math.sin(a) * d, life: 22, arm: 0.4 });
    }
  }
  function updateMines(dt) {
    for (let i = mines.length - 1; i >= 0; i--) {
      const m = mines[i];
      setActor(ownerOf(m.o));
      const st = ST;
      m.life -= dt;
      m.arm -= dt;
      let trigger = m.life <= 0;
      if (m.arm <= 0 && !trigger) near(m.x, m.y, 12, () => { trigger = true; return false; });
      if (trigger) {
        explosion(m.x, m.y, st.mineRad, st.mineDmg, '#ff5a4a');
        mines[i] = mines[mines.length - 1];
        mines.pop();
      }
    }
  }

  function updateNovas(dt) {
    for (let i = novas.length - 1; i >= 0; i--) {
      const n = novas[i];
      setActor(ownerOf(n.o));
      n.r += n.speed * dt;
      for (const e of enemies) {
        if (e.dead || n.hit.has(e)) continue;
        const d = Math.hypot(e.x - n.x, e.y - n.y);
        if (d < n.r + e.r) {
          n.hit.add(e);
          dealDamage(e, n.dmg, { crit: true, color: 4 });
          if (!e.boss && d > 0) {
            e.vx += ((e.x - n.x) / d) * n.knock;
            e.vy += ((e.y - n.y) / d) * n.knock;
          }
        }
      }
      if (n.r >= n.max) { novas[i] = novas[novas.length - 1]; novas.pop(); }
    }
  }
  function addNova(x, y, radius, dmg, knock, color) {
    novas.push({ o: p.idx, x, y, r: 4, max: radius, dmg, knock, speed: radius * 3, hit: new Set(), color: color || '#7ff0ff' });
    sfx('nova');
  }

  function orbitDrones(dt) {
    const orbitR = 26;
    for (const d of droneList) {
      d.offset += dt * 1.8;
      const tx = p.x + Math.cos(d.offset) * orbitR;
      const ty = p.y + Math.sin(d.offset) * orbitR;
      d.x += (tx - d.x) * Math.min(1, dt * 14);
      d.y += (ty - d.y) * Math.min(1, dt * 14);
    }
  }

  function updateDrones(dt) {
    const st = ST;
    orbitDrones(dt);
    for (const d of droneList) {
      d.fireT -= dt;
      if (d.fireT <= 0) {
        const e = nearest(d.x, d.y, st.droneRange);
        if (e) {
          d.fireT = 1 / st.droneRate;
          const a = Math.atan2(e.y - d.y, e.x - d.x);
          addBullet(d.x, d.y, a, 300, st.droneDmg, e, { range: st.droneRange * 1.3, pierce: 0, bounce: 0, crit: st.droneCrit, color: '#9cffb0', drone: true });
        }
      }
      if (st.droneArc) {
        d.arcT -= dt;
        if (d.arcT <= 0) {
          d.arcT = 3;
          fireArcFrom(d.x, d.y, 1, Math.max(st.arcDmg * 0.5, st.droneDmg * 2));
        }
      }
      if (st.droneRam > 0) {
        d.ramT -= dt;
        if (d.ramT <= 0) {
          let any = false;
          near(d.x, d.y, 5, e => { dealDamage(e, st.cannonDmg * st.droneRam, { quiet: true }); any = true; });
          if (any) d.ramT = 0.3;
        }
      }
    }
    if (st.droneBlock) {
      for (let i = eBullets.length - 1; i >= 0; i--) {
        const b = eBullets[i];
        for (const d of droneList) {
          if (Math.abs(b.x - d.x) < 6 && Math.abs(b.y - d.y) < 6) {
            spark(b.x, b.y, '#9cffb0');
            eBullets[i] = eBullets[eBullets.length - 1];
            eBullets.pop();
            break;
          }
        }
      }
    }
  }

  function updateTrail(dt) {
    const st = ST;
    if (!st.trail) return;
    const sp = Math.hypot(p.vx, p.vy);
    p.trailT -= dt;
    if (p.trailT <= 0 && sp > 40) {
      p.trailT = 0.1;
      if (p.patches.length >= 36) p.patches.shift();
      p.patches.push({ x: p.x, y: p.y, life: 2, r: 8, hitT: 0 });
    }
    for (let i = p.patches.length - 1; i >= 0; i--) {
      const c = p.patches[i];
      c.life -= dt;
      c.hitT -= dt;
      if (c.hitT <= 0) {
        c.hitT = 0.3;
        near(c.x, c.y, c.r, e => { dealDamage(e, st.cannonDmg * st.trailDmg, { quiet: true, color: 1 }); });
      }
      if (c.life <= 0) p.patches.splice(i, 1);
    }
  }

  /* ---------- Joueur ---------- */
  function tryDash(mv) {
    const st = ST;
    if (!st.dash || p.charges <= 0 || p.dashT > 0) return;
    let dx = mv.x, dy = mv.y;
    if (Math.abs(dx) + Math.abs(dy) < 0.1) { dx = Math.cos(p.ang); dy = Math.sin(p.ang); }
    const l = Math.hypot(dx, dy) || 1;
    p.dashVX = (dx / l) * 620;
    p.dashVY = (dy / l) * 620;
    p.dashT = st.dashLen;
    p.charges--;
    p.dashHit = new Set();
    sfx('dash');
    burst(p.x, p.y, 14, ['#c8f4ff', '#4ad6ff'], 90, 0.3);
    shake = Math.max(shake, 1);
  }

  /* Pilotage local : le seul morceau que l'invité simule lui-même, pour répondre sans délai. */
  function moveShip(dt, mv) {
    const st = ST;
    if (Input.dashQueued) { tryDash(mv); Input.dashQueued = false; }
    if (st.dash && p.charges < st.dashCharges) {
      p.dashCd += dt;
      if (p.dashCd >= st.dashCd) { p.charges++; p.dashCd = 0; }
    }

    if (p.dashT > 0) {
      p.dashT -= dt;
      p.x += p.dashVX * dt;
      p.y += p.dashVY * dt;
      p.vx = p.dashVX * 0.3;
      p.vy = p.dashVY * 0.3;
      spark(p.x, p.y, '#4ad6ff');
      spark(p.x, p.y, '#ffffff');
      if (mode !== 'guest') dashEffects(p.dashT <= 0);
    } else {
      // Pilotage à l'ancienne : on pousse, le vaisseau glisse.
      const tvx = mv.x * st.speed, tvy = mv.y * st.speed;
      const ax = tvx - p.vx, ay = tvy - p.vy;
      const al = Math.hypot(ax, ay);
      const maxA = (Math.abs(mv.x) + Math.abs(mv.y) > 0 ? st.accel : st.accel * 0.55) * dt;
      if (al > maxA) { p.vx += (ax / al) * maxA; p.vy += (ay / al) * maxA; }
      else { p.vx = tvx; p.vy = tvy; }
      p.x += p.vx * dt;
      p.y += p.vy * dt;
    }
    p.thrust = Math.abs(mv.x) + Math.abs(mv.y) > 0.05 ? 1 : 0;

    if (p.thrust && parts.length < 700) {
      const a = p.ang + Math.PI / 2;
      const tx = p.x + Math.cos(a) * 7 + rnd(-1, 1), ty = p.y + Math.sin(a) * 7 + rnd(-1, 1);
      parts.push({ x: tx, y: ty, vx: Math.cos(a) * 40 + rnd(-10, 10), vy: Math.sin(a) * 40 + rnd(-10, 10), t: rnd(0.1, 0.25), c: pick(['#ffe14a', '#ff9d2e', '#ff4a4a']), z: 1 });
    }
  }

  function dashEffects(ended) {
    const st = ST;
    if (st.dashDmg > 0) {
      if (!p.dashHit) p.dashHit = new Set();
      near(p.x, p.y, 12, e => {
        if (p.dashHit.has(e)) return;
        p.dashHit.add(e);
        dealDamage(e, st.cannonDmg * st.dashDmg, { crit: true });
      });
    }
    if (ended && st.dashNova) explosion(p.x, p.y, 62, st.cannonDmg * 4, '#4ad6ff', { knock: 150 });
  }

  function updatePlayer(dt) {
    const st = ST;
    let mv = null;
    if (p.remote) {
      // L'invité pilote de son côté ; on prolonge sa trajectoire entre deux messages.
      p.x += p.vx * dt;
      p.y += p.vy * dt;
      p.thrust = Math.hypot(p.vx, p.vy) > 10 ? 1 : 0;
      const wasDashing = p.dashT > 0;
      p.dashT = p.netDash ? 0.05 : 0;
      if (p.netDash) dashEffects(false);
      else if (wasDashing) { dashEffects(true); p.dashHit = null; }
    } else {
      mv = moveVector();
      moveShip(dt, mv);
    }

    // Le boss passe en priorité, sauf si un ennemi est sur le point de nous toucher.
    let target = nearest(p.x, p.y, st.range * 1.05);
    const closeBoss = nearestBoss(p.x, p.y);
    if (closeBoss && Math.hypot(closeBoss.x - p.x, closeBoss.y - p.y) < st.range * 1.05 + closeBoss.r) {
      const close = target && Math.hypot(target.x - p.x, target.y - p.y) < 42;
      if (!close) target = closeBoss;
    }
    let wantAim = p.aim;
    let shouldFire = false;
    const manualAim = p.remote ? p.netAim
      : S.set.aim === 'mouse' && Input.mouseSeen ? Math.atan2(Input.my + camY - p.y, Input.mx + camX - p.x) : null;
    if (manualAim !== null) {
      wantAim = manualAim;
      shouldFire = true;
    } else if (target) {
      // Tir anticipé : on vise là où l'ennemi sera.
      const d = Math.hypot(target.x - p.x, target.y - p.y);
      const lead = d / st.bulletSpeed;
      wantAim = Math.atan2(target.y + target.vy * lead - p.y, target.x + target.vx * lead - p.x);
      shouldFire = true;
    } else if (p.thrust) {
      wantAim = mv ? Math.atan2(mv.y, mv.x) : Math.atan2(p.vy, p.vx);
    }
    let d = wantAim - p.aim;
    while (d > Math.PI) d -= TAU;
    while (d < -Math.PI) d += TAU;
    p.aim += clamp(d, -14 * dt, 14 * dt);
    p.ang = p.aim;

    // Canon
    const frenzyBoost = 1 + p.frenzy * 0.01;
    p.fireT -= dt;
    if (shouldFire && p.fireT <= 0) {
      p.fireT = 1 / (st.rate * frenzyBoost);
      fireCannon(target);
    }

    // Frénésie qui retombe
    if (p.frenzyT > 0) p.frenzyT -= dt;
    else if (p.frenzy > 0) p.frenzy = Math.max(0, p.frenzy - dt * 6);

    // Armes secondaires
    if (st.missile) {
      p.missileT -= dt;
      if (p.missileT <= 0 && launchMissiles()) p.missileT = st.missileCd;
    }
    if (st.mine) {
      p.mineT -= dt;
      if (p.mineT <= 0) { p.mineT = st.mineCd; dropMines(); }
    }
    if (st.arc) {
      p.arcT -= dt;
      if (p.arcT <= 0) {
        let ok = false;
        for (let b = 0; b < st.arcBolts; b++) ok = fireArcFrom(p.x, p.y, st.arcChain, st.arcDmg) || ok;
        if (ok) p.arcT = st.arcCd;
      }
    }
    if (st.nova) {
      p.novaT -= dt;
      if (p.novaT <= 0 && nearest(p.x, p.y, st.novaRad * 0.9)) {
        p.novaT = st.novaCd;
        addNova(p.x, p.y, st.novaRad, st.novaDmg, st.novaKnock);
      }
    }
    if (st.beam) fireBeam(dt);

    // Réparation & bouclier
    if (st.regen > 0 && p.hull < st.maxHull) p.hull = Math.min(st.maxHull, p.hull + st.maxHull * st.regen * dt);
    if (st.shield) {
      p.shieldT -= dt;
      const maxS = st.maxHull * st.shieldMul;
      if (p.shieldT <= 0 && p.shield < maxS) p.shield = Math.min(maxS, p.shield + maxS * st.shieldRegen * dt);
    }
    if (p.invuln > 0) p.invuln -= dt;
    if (p.flash > 0) p.flash -= dt;
  }

  function hurtPlayer(amount, source) {
    if (p.invuln > 0 || p.dashT > 0 || p.dead) return;
    const st = ST;
    if (Math.random() < st.dodge) {
      p.invuln = 0.15;
      burst(p.x, p.y, 5, ['#ffffff'], 60, 0.2);
      return;
    }
    let dmg = amount * st.armorMul;
    if (source === 'contact' && st.ram) dmg *= 0.7;
    if (st.shield && p.shield > 0) {
      p.shieldT = 3.5;
      const left = p.shield - dmg;
      p.shield = Math.max(0, left);
      if (p === me) sfx('shieldHit'); else Coop.queue(['s', 'shieldHit']);
      p.invuln = st.invuln * 0.6;
      ringAt(p.x, p.y, 16, '#4ad6ff');
      if (left <= 0) {
        if (st.shieldNova) addNova(p.x, p.y, 110, st.cannonDmg * 12, 260, '#4ad6ff');
        dmg = -left;
        if (dmg <= 0) return;
      } else return;
    }
    if (st.shield) p.shieldT = 3.5;
    p.hull -= dmg;
    p.invuln = st.invuln;
    p.flash = 0.2;
    burst(p.x, p.y, 8, ['#ff4a4a', '#ffffff'], 80, 0.3);
    if (p === me) { shake = Math.max(shake, 3); sfx('hurt'); UI.hurtFlash(); }
    else Coop.queue(['h']);
    if (p.hull <= 0) {
      if (p.revives > 0) {
        p.revives--;
        p.hull = st.maxHull * 0.5;
        p.invuln = 2;
        addNova(p.x, p.y, 180, st.cannonDmg * 15, 320, '#ffffff');
        eBullets.length = 0;
        sayBanner('CAPSULE ÉJECTÉE', 'Dernière chance');
      } else {
        killPlayer();
      }
    }
  }

  function killPlayer() {
    p.dead = true;
    p.hull = 0;
    p.rescue = 0;
    p.beam = null;
    burst(p.x, p.y, 110, ['#ffffff', '#4ad6ff', '#ff9d2e', '#ff4a4a'], 200, 1.2);
    ringAt(p.x, p.y, 90, '#4ad6ff');
    sfx('death');
    if (p === me) shake = 10;
    if (players.every(s => s.dead)) {
      run.over = true;
      run.deathT = 1.6;
      sayMusic('stop');
    } else {
      sayToast('Vaisseau à terre : rejoignez-le pour le réparer !');
    }
  }

  /* Un vaisseau tombé revient quand son coéquipier reste près de lui, ou au secteur suivant.
     Chaque réparation pendant un même vol prend deux fois plus de temps : 3 s, 6 s, 12 s… */
  function reviveShip(s, frac, byAlly) {
    s.dead = false;
    s.hull = s.st.maxHull * frac;
    s.invuln = 2;
    s.rescue = 0;
    if (byAlly) {
      s.rescues++;
      s.rescueNeed = RESCUE_BASE * Math.pow(2, s.rescues);
    }
    ringAt(s.x, s.y, 60, '#6cf06c');
    sayToast(byAlly ? `Vaisseau réparé ! La prochaine réparation prendra ${s.rescueNeed} s` : 'Vaisseau réparé !');
  }
  function updateRescue(dt) {
    if (!inCoop()) return;
    for (const s of players) {
      if (!s.dead) continue;
      const ally = nearestAlive(s.x, s.y);
      const close = !ally.dead && Math.hypot(ally.x - s.x, ally.y - s.y) < RESCUE_RADIUS;
      // S'éloigner un instant ne fait pas tout perdre : la jauge redescend lentement.
      s.rescue = close ? s.rescue + dt : Math.max(0, s.rescue - dt * 0.5);
      if (s.rescue >= s.rescueNeed) reviveShip(s, 0.4, true);
    }
  }

  function endRun(abandoned) {
    // Rien n'est perdu : ce qui traîne encore est ramassé.
    for (const o of orbs) collectOrb(o);
    orbs.length = 0;
    const st = me.st;
    let bonus = 0;
    if (st.interest > 0) {
      bonus = run.units * st.interest;
      S.units += bonus;
      S.lifeUnits += bonus;
      S.ascUnits += bonus;
    }
    Save.write();
    const summary = {
      time: run.time, kills: run.kills, units: run.units, bonus, cores: run.cores,
      sector: run.sector, bosses: run.bossesKilled, best: S.best, bestCombo: run.bestCombo, abandoned: !!abandoned,
    };
    if (mode === 'host') Coop.hostOver(summary);
    UI.showOver(summary);
  }

  /* Fin du vol vue par l'invité. */
  function guestEnd(r, lost) {
    if (!me) return;
    let bonus = 0;
    if (me.st.interest > 0) {
      bonus = run.units * me.st.interest;
      S.units += bonus;
      S.lifeUnits += bonus;
      S.ascUnits += bonus;
    }
    const num = v => Number(v) || 0; // ces valeurs viennent de l'autre appareil
    S.kills += num(r.kills);
    Save.write();
    const summary = {
      time: num(r.time), kills: num(r.kills), units: run.units, bonus, cores: run.cores, sector: num(r.sector),
      bosses: num(r.bosses), best: S.best, bestCombo: num(r.bestCombo), lost: !!lost, abandoned: !!r.abandoned,
    };
    clearAll();
    UI.showOver(summary);
  }

  /* ---------- Pas de simulation ---------- */
  function step(rawDt) {
    if (!me || !run) return;
    time += rawDt;
    if (run.over) {
      run.deathT -= rawDt;
      updateFx(rawDt);
      for (const e of enemies) { e.x += e.vx * rawDt * 0.3; e.y += e.vy * rawDt * 0.3; }
      if (run.deathT <= 0) { endRun(); clearAll(); }
      return;
    }

    let dt = rawDt;
    if (me.st.dilate && !me.dead && me.hull < me.st.maxHull * 0.3) dt *= 0.7;

    run.t += dt;
    run.time += dt;
    if (run.comboT > 0) { run.comboT -= dt; if (run.comboT <= 0) run.combo = 0; }

    for (const s of players) {
      if (s.dead) continue;
      setActor(s);
      updatePlayer(dt);
    }
    rebuildGrid();

    for (let i = 0; i < enemies.length; i++) {
      setActor(nearestAlive(enemies[i].x, enemies[i].y));
      updateEnemy(enemies[i], dt);
    }
    separateEnemies(dt);
    rebuildGrid();

    updateBullets(dt);
    updateMissiles(dt);
    updateMines(dt);
    updateNovas(dt);
    for (const s of players) {
      if (s.dead) continue;
      setActor(s);
      updateDrones(dt);
      updateTrail(dt);
    }
    updateContacts();
    updateEnemyBullets(dt);
    updateOrbs(dt);
    updateRescue(dt);
    updateSpawns(dt);
    setActor(me);

    // Nettoyage des morts
    for (let i = enemies.length - 1; i >= 0; i--) {
      if (enemies[i].dead) {
        enemies[i] = enemies[enemies.length - 1];
        enemies.pop();
      }
    }
    updateFx(rawDt);
  }

  function updateBullets(dt) {
    for (let i = pBullets.length - 1; i >= 0; i--) {
      const b = pBullets[i];
      setActor(ownerOf(b.o));
      const st = ST;
      b.life -= dt;
      let dead = b.life <= 0;
      if (!dead) {
        if (st.homing && !b.shard && !b.drone) {
          // Un obus parti sans cible (tourelle arrière, canons latéraux, tir renvoyé) en cherche une aussi.
          if (!b.target || b.target.dead) b.target = nearest(b.x, b.y, 80);
          if (b.target && !b.target.dead) {
            const want = Math.atan2(b.target.y - b.y, b.target.x - b.x);
            const cur = Math.atan2(b.vy, b.vx);
            let d = want - cur;
            while (d > Math.PI) d -= TAU;
            while (d < -Math.PI) d += TAU;
            const na = cur + clamp(d, -5 * dt, 5 * dt);
            b.vx = Math.cos(na) * b.sp;
            b.vy = Math.sin(na) * b.sp;
          }
        }
        b.x += b.vx * dt;
        b.y += b.vy * dt;
        near(b.x, b.y, 2, e => {
          if (b.hit && b.hit.has(e)) return;
          dealDamage(e, b.dmg, { crit: b.crit, slow: st.cryo, color: b.drone ? 3 : 0, quiet: b.shard });
          if (st.explosive > 0 && !b.shard && !b.drone && Math.random() < st.explosive) {
            explosion(b.x, b.y, 22, b.dmg * 0.5, '#ffb24a');
          }
          if (!b.hit) b.hit = new Set();
          b.hit.add(e);
          spark(b.x, b.y, '#ffffff');
          if (b.pierce > 0) { b.pierce--; return; }
          if (b.bounce > 0) {
            b.bounce--;
            const next = nearest(b.x, b.y, 130, b.hit);
            if (next) {
              const a = Math.atan2(next.y - b.y, next.x - b.x);
              b.vx = Math.cos(a) * b.sp;
              b.vy = Math.sin(a) * b.sp;
              b.life = Math.max(b.life, 0.45);
              b.target = next;
              return false;
            }
          }
          dead = true;
          return false;
        });
      }
      if (dead) {
        pBullets[i] = pBullets[pBullets.length - 1];
        pBullets.pop();
      }
    }
  }

  function updateContacts() {
    for (const s of players) {
      if (s.dead) continue;
      setActor(s);
      const st = ST;
      near(s.x, s.y, 6, e => {
        if (e.t.ai === 'flee') return;
        const wasInv = s.invuln > 0 || s.dashT > 0;
        if (!wasInv) {
          hurtPlayer(e.dmg, 'contact');
          if (st.thorns > 0) dealDamage(e, st.cannonDmg * st.thorns, { quiet: false, color: 1 });
          if (st.ram) dealDamage(e, st.cannonDmg * 8, { crit: true, color: 5 });
        }
        if (!s.dead && e.t.dieOnHit && !wasInv) {
          killEnemy(e);
        } else if (!e.boss && !e.dead) {
          const dx = e.x - s.x, dy = e.y - s.y;
          const d = Math.hypot(dx, dy) || 1;
          e.vx = (dx / d) * 160;
          e.vy = (dy / d) * 160;
        }
      });
    }
  }

  function updateEnemyBullets(dt) {
    for (let i = eBullets.length - 1; i >= 0; i--) {
      const b = eBullets[i];
      b.life -= dt;
      b.x += b.vx * dt;
      b.y += b.vy * dt;
      let dead = b.life <= 0;
      if (!dead) {
        for (const s of players) {
          if (s.dead) continue;
          const dx = b.x - s.x, dy = b.y - s.y;
          if (dx * dx + dy * dy >= (5 + b.r) * (5 + b.r)) continue;
          if (s.invuln > 0 || s.dashT > 0) continue;
          setActor(s);
          const st = ST;
          if (st.reflect > 0 && Math.random() < st.reflect) {
            addBullet(b.x, b.y, Math.atan2(-b.vy, -b.vx), 300, st.cannonDmg * 2, null, { pierce: 0, bounce: 0, color: '#7ff0ff' });
            ringAt(s.x, s.y, 14, '#7ff0ff');
          } else {
            hurtPlayer(b.dmg, 'bullet');
            // Une capsule de secours efface tous les tirs : il ne reste rien à parcourir.
            if (!eBullets.length) return;
          }
          dead = true;
          break;
        }
      }
      if (dead) {
        eBullets[i] = eBullets[eBullets.length - 1];
        eBullets.pop();
      }
    }
  }

  function updateFx(dt) {
    for (let i = parts.length - 1; i >= 0; i--) {
      const q = parts[i];
      q.t -= dt;
      if (q.t <= 0) { parts[i] = parts[parts.length - 1]; parts.pop(); continue; }
      q.x += q.vx * dt;
      q.y += q.vy * dt;
      q.vx *= 1 - dt * 2.2;
      q.vy *= 1 - dt * 2.2;
    }
    for (let i = rings.length - 1; i >= 0; i--) {
      const r = rings[i];
      r.t += dt;
      r.r += (r.max - r.r) * Math.min(1, dt * 9);
      if (r.t > 0.32) { rings[i] = rings[rings.length - 1]; rings.pop(); }
    }
    for (let i = bolts.length - 1; i >= 0; i--) {
      bolts[i].t -= dt;
      if (bolts[i].t <= 0) { bolts[i] = bolts[bolts.length - 1]; bolts.pop(); }
    }
    for (let i = texts.length - 1; i >= 0; i--) {
      const q = texts[i];
      q.t -= dt;
      q.y -= dt * 22;
      if (q.t <= 0) { texts[i] = texts[texts.length - 1]; texts.pop(); }
    }
    shake = Math.max(0, shake - dt * 18);
  }

  /* ---------- Rendu ---------- */
  function drawStars() {
    const sector = run ? run.sector : 1;
    const neb = nebulae[(sector - 1) % nebulae.length];
    ctx.fillStyle = '#05060f';
    ctx.fillRect(0, 0, VW, VH);
    if (neb) {
      const size = neb.width;
      const ox = -(((camX * 0.12) % size) + size) % size;
      const oy = -(((camY * 0.12) % size) + size) % size;
      for (let x = Math.floor(ox); x < VW; x += size) {
        for (let y = Math.floor(oy); y < VH; y += size) ctx.drawImage(neb, x, y);
      }
    }
    const speeds = [0.2, 0.4, 0.7];
    const colors = [['#3a3f66', '#2b2f4e'], ['#7078a8', '#565c88'], ['#d8e2ff', '#a9b6e8']];
    for (let l = 0; l < 3; l++) {
      const list = stars[l];
      for (let i = 0; i < list.length; i++) {
        const s = list[i];
        const size = 1024;
        const x = (((s.x - camX * speeds[l]) % size) + size) % size;
        const y = (((s.y - camY * speeds[l]) % size) + size) % size;
        if (x >= VW || y >= VH) continue;
        ctx.fillStyle = colors[l][Math.sin(time * 2 + s.tw) > 0.6 ? 1 : 0];
        ctx.fillRect(x | 0, y | 0, 1, 1);
      }
    }
  }

  function drawSprite(img, x, y, ang, scale = 1) {
    const w = img.width * scale, h = img.height * scale;
    const sx = Math.round(x - camX), sy = Math.round(y - camY);
    if (sx < -w || sx > VW + w || sy < -h || sy > VH + h) return;
    if (!ang) {
      ctx.drawImage(img, sx - (w >> 1), sy - (h >> 1), w, h);
      return;
    }
    const step = TAU / 32;
    const a = Math.round(ang / step) * step;
    const c = Math.cos(a), s = Math.sin(a);
    ctx.setTransform(c, s, -s, c, sx, sy);
    ctx.drawImage(img, -w / 2, -h / 2, w, h);
    ctx.setTransform(1, 0, 0, 1, 0, 0);
  }

  function pxLine(x0, y0, x1, y1, color, thick = 1) {
    ctx.fillStyle = color;
    let x = Math.round(x0), y = Math.round(y0);
    const X = Math.round(x1), Y = Math.round(y1);
    const dx = Math.abs(X - x), dy = Math.abs(Y - y);
    const sx = x < X ? 1 : -1, sy = y < Y ? 1 : -1;
    let err = dx - dy;
    let guard = 0;
    while (guard++ < 2000) {
      ctx.fillRect(x, y, thick, thick);
      if (x === X && y === Y) break;
      const e2 = err * 2;
      if (e2 > -dy) { err -= dy; x += sx; }
      if (e2 < dx) { err += dx; y += sy; }
    }
  }

  function pxCircle(cx, cy, r, color, gap = 1) {
    ctx.fillStyle = color;
    const n = Math.max(10, Math.floor((TAU * r) / (1 + gap)));
    for (let i = 0; i < n; i++) {
      const a = (i / n) * TAU;
      ctx.fillRect(Math.round(cx + Math.cos(a) * r), Math.round(cy + Math.sin(a) * r), 1, 1);
    }
  }

  function draw() {
    if (!ctx) return;
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    if (!me && !run) { camX = time * 8; camY = time * 3; drawStars(); return; }
    setActor(me);
    const focus = me;
    const sh = S.set.shake ? shake : 0;
    camX = Math.round(focus.x - VW / 2 + rnd(-sh, sh));
    camY = Math.round(focus.y - VH / 2 + rnd(-sh, sh));
    drawStars();

    // Traînée plasma
    for (const ship of players) for (const c of ship.patches) {
      const r = c.r * clamp(c.life, 0.2, 1);
      ctx.fillStyle = c.life > 1 ? '#ff6cd0' : c.life > 0.5 ? '#b02a8c' : '#5a1a50';
      const sx = c.x - camX, sy = c.y - camY;
      for (let i = 0; i < 4; i++) {
        const a = (time * 3 + i * 1.57 + c.x);
        ctx.fillRect(Math.round(sx + Math.cos(a) * r * 0.6), Math.round(sy + Math.sin(a) * r * 0.6), 2, 2);
      }
    }

    // Mines
    for (const m of mines) {
      const blink = m.arm <= 0 && Math.floor(time * 5 + m.x) % 2 === 0;
      drawSprite(blink ? Sprites.mine.w : Sprites.mine.n, m.x, m.y, 0);
    }

    // Orbes
    for (const o of orbs) {
      const sx = Math.round(o.x - camX), sy = Math.round(o.y - camY);
      if (sx < -4 || sx > VW + 4 || sy < -4 || sy > VH + 4) continue;
      if (o.kind === 'c') {
        ctx.fillStyle = '#d86cff';
        ctx.fillRect(sx - 2, sy - 1, 5, 3);
        ctx.fillRect(sx - 1, sy - 2, 3, 5);
        ctx.fillStyle = '#ffffff';
        ctx.fillRect(sx, sy, 1, 1);
      } else {
        const pulse = Math.floor(time * 8 + o.x) % 2;
        ctx.fillStyle = pulse ? '#ffe14a' : '#ffb82a';
        ctx.fillRect(sx - 1, sy - 1, 3, 3);
        ctx.fillStyle = '#fff6b0';
        ctx.fillRect(sx, sy, 1, 1);
      }
    }

    // Ennemis
    for (const e of enemies) {
      if (e.dead) continue;
      const set = Sprites[e.t.sprite];
      const img = e.flash > 0 ? set.w : e.elite ? set.e : set.n;
      drawSprite(img, e.x, e.y, e.t.noRot ? 0 : e.ang, e.drawScale);
      if (e.elite) pxCircle(e.x - camX, e.y - camY, e.r + 3 + Math.sin(time * 6), '#ffd84a', 3);
      // Barre de vie des gros ennemis touchés
      if (!e.boss && e.maxHp > 0 && e.hp < e.maxHp && e.r > 6) {
        const w = Math.round(e.r * 2);
        const sx = Math.round(e.x - camX - w / 2), sy = Math.round(e.y - camY - e.r - 4);
        ctx.fillStyle = '#30304a';
        ctx.fillRect(sx, sy, w, 1);
        ctx.fillStyle = '#6cf06c';
        ctx.fillRect(sx, sy, Math.ceil(w * (e.hp / e.maxHp)), 1);
      }
      // Annonce de la charge du titan
      if (e.boss && e.t.ai === 'ram' && e.state === 1) {
        const c = Math.floor(time * 16) % 2 ? '#ff4a4a' : '#ff9d2e';
        pxLine(e.x - camX, e.y - camY, e.x - camX + e.cx * 260, e.y - camY + e.cy * 260, c);
      }
    }

    // Missiles
    for (const m of missiles) {
      const sx = Math.round(m.x - camX), sy = Math.round(m.y - camY);
      ctx.fillStyle = '#ffffff';
      ctx.fillRect(sx - 1, sy - 1, 2, 2);
      ctx.fillStyle = '#ff5a4a';
      ctx.fillRect(Math.round(sx - Math.cos(m.ang) * 2), Math.round(sy - Math.sin(m.ang) * 2), 2, 2);
    }

    // Tirs du joueur
    for (const b of pBullets) {
      const sx = b.x - camX, sy = b.y - camY;
      if (sx < -4 || sx > VW + 4 || sy < -4 || sy > VH + 4) continue;
      ctx.fillStyle = b.color;
      const k = 0.012;
      ctx.fillRect(Math.round(sx), Math.round(sy), 2, 2);
      ctx.fillRect(Math.round(sx - b.vx * k), Math.round(sy - b.vy * k), 1, 1);
    }

    // Tirs ennemis
    for (const b of eBullets) {
      const sx = Math.round(b.x - camX), sy = Math.round(b.y - camY);
      if (sx < -4 || sx > VW + 4 || sy < -4 || sy > VH + 4) continue;
      const s = b.r * 2;
      ctx.fillStyle = b.color;
      ctx.fillRect(sx - b.r, sy - b.r, s, s);
      ctx.fillStyle = '#ffffff';
      ctx.fillRect(sx - (b.r >> 1), sy - (b.r >> 1), Math.max(1, b.r), Math.max(1, b.r));
    }

    // Rayons
    for (const s of players) {
      if (s.dead || !s.beam) continue;
      const x0 = s.x - camX, y0 = s.y - camY;
      const x1 = x0 + Math.cos(s.beam.a) * s.beam.len, y1 = y0 + Math.sin(s.beam.a) * s.beam.len;
      const w = s.beam.w;
      pxLine(x0, y0, x1, y1, '#2a8cc8', Math.max(1, w));
      pxLine(x0, y0, x1, y1, Math.floor(time * 20) % 2 ? '#c8f4ff' : '#ffffff', Math.max(1, w - 2));
    }

    // Arcs
    for (const b of bolts) {
      for (let i = 0; i + 3 < b.pts.length; i += 2) {
        const x0 = b.pts[i] - camX, y0 = b.pts[i + 1] - camY, x1 = b.pts[i + 2] - camX, y1 = b.pts[i + 3] - camY;
        const seg = 4;
        let px = x0, py = y0;
        for (let k = 1; k <= seg; k++) {
          const f = k / seg;
          const j = k === seg ? 0 : 5;
          const nx = x0 + (x1 - x0) * f + rnd(-j, j), ny = y0 + (y1 - y0) * f + rnd(-j, j);
          pxLine(px, py, nx, ny, b.color);
          px = nx; py = ny;
        }
      }
    }

    // Joueurs
    for (const s of players) drawShip(s);
    setActor(me);

    // Novas
    for (const n of novas) {
      const a = 1 - n.r / n.max;
      pxCircle(n.x - camX, n.y - camY, n.r, a > 0.4 ? '#ffffff' : n.color, 1);
      pxCircle(n.x - camX, n.y - camY, n.r * 0.92, n.color, 2);
    }
    // Anneaux
    for (const r of rings) {
      pxCircle(r.x - camX, r.y - camY, r.r, r.t < 0.14 ? '#ffffff' : r.c, r.t < 0.18 ? 1 : 3);
    }
    // Particules
    for (const q of parts) {
      const sx = Math.round(q.x - camX), sy = Math.round(q.y - camY);
      if (sx < 0 || sy < 0 || sx > VW || sy > VH) continue;
      ctx.fillStyle = q.c;
      ctx.fillRect(sx, sy, q.z, q.z);
    }
    // Chiffres
    for (const q of texts) drawMini(ctx, q.s, q.x - camX, q.y - camY, q.c);

    drawIndicators();

    // Stick tactile
    if (Input.stick) {
      const s = Input.stick;
      pxCircle(s.ox, s.oy, 22, '#4ad6ff', 3);
      const d = Math.hypot(s.x - s.ox, s.y - s.oy);
      const m = d > 22 ? 22 / d : 1;
      ctx.fillStyle = '#c8f4ff';
      ctx.fillRect(Math.round(s.ox + (s.x - s.ox) * m) - 3, Math.round(s.oy + (s.y - s.oy) * m) - 3, 6, 6);
    }
    // Réticule souris
    if (S.set.aim === 'mouse' && Input.mouseSeen && me) {
      ctx.fillStyle = '#ffe14a';
      const mx = Math.round(Input.mx), my = Math.round(Input.my);
      ctx.fillRect(mx - 4, my, 3, 1);
      ctx.fillRect(mx + 2, my, 3, 1);
      ctx.fillRect(mx, my - 4, 1, 3);
      ctx.fillRect(mx, my + 2, 1, 3);
    }
  }

  function drawShip(s) {
    setActor(s);
    const st = ST;
    if (s.dead) {
      // Épave clignotante, avec la jauge de réparation autour.
      if (Math.floor(time * 4) % 2 === 0) drawSprite((s.idx === 1 ? Sprites.ship2 : Sprites.ship).e, s.x, s.y, s.ang + Math.PI / 2);
      // Zone de réparation, et sa jauge qui se remplit.
      pxCircle(s.x - camX, s.y - camY, RESCUE_RADIUS, '#30304a', 5);
      const frac = clamp(s.rescue / s.rescueNeed, 0, 1);
      if (frac > 0) {
        const n = Math.floor(frac * 36);
        ctx.fillStyle = '#6cf06c';
        for (let i = 0; i < n; i++) {
          const a = -Math.PI / 2 + (i / 36) * TAU;
          ctx.fillRect(Math.round(s.x - camX + Math.cos(a) * 18), Math.round(s.y - camY + Math.sin(a) * 18), 2, 2);
        }
      }
      return;
    }
    // Bouclier
    if (st.shield && s.shield > 0) {
      const c = s.shieldT > 3 ? '#ffffff' : '#4ad6ff';
      pxCircle(s.x - camX, s.y - camY, 13, c, 2 + Math.floor((1 - s.shield / (st.maxHull * st.shieldMul)) * 3));
    }
    const blinking = s.invuln > 0 && Math.floor(time * 20) % 2 === 0 && s.dashT <= 0;
    if (!blinking) {
      const set = s.idx === 1 ? Sprites.ship2 : Sprites.ship;
      drawSprite(s.flash > 0 ? set.w : set.n, s.x, s.y, s.ang + Math.PI / 2);
      drawPods();
    }
    // Jauge de saut
    if (s === me && st.dash) {
      const sx = Math.round(s.x - camX), sy = Math.round(s.y - camY) + 12;
      const n = st.dashCharges;
      for (let i = 0; i < n; i++) {
        ctx.fillStyle = i < s.charges ? '#4ad6ff' : '#1a3f7a';
        ctx.fillRect(sx - n * 2 + i * 4, sy, 3, 1);
      }
    }
    for (const d of s.drones) drawSprite(Sprites.drone.n, d.x, d.y, 0);
  }

  /* Le vaisseau s'équipe visuellement selon ce qu'on débloque. */
  function drawPods() {
    const st = ST;
    const sx = Math.round(p.x - camX), sy = Math.round(p.y - camY);
    const step = TAU / 32;
    const a = Math.round((p.ang + Math.PI / 2) / step) * step;
    const c = Math.cos(a), s = Math.sin(a);
    ctx.setTransform(c, s, -s, c, sx, sy);
    if (st.salvo >= 2) { ctx.fillStyle = '#ffffff'; ctx.fillRect(-4, -6, 1, 3); ctx.fillRect(4, -6, 1, 3); }
    if (st.salvo >= 3) { ctx.fillStyle = '#ffe14a'; ctx.fillRect(-6, -3, 1, 3); ctx.fillRect(6, -3, 1, 3); }
    if (st.salvo >= 4) { ctx.fillStyle = '#ff5a4a'; ctx.fillRect(-8, -1, 1, 3); ctx.fillRect(8, -1, 1, 3); }
    if (st.side) { ctx.fillStyle = '#ff9d2e'; ctx.fillRect(-9, 2, 2, 2); ctx.fillRect(8, 2, 2, 2); }
    if (st.rear) { ctx.fillStyle = '#ff5a4a'; ctx.fillRect(-1, 7, 3, 2); }
    if (st.missile) { ctx.fillStyle = '#c8f4ff'; ctx.fillRect(-5, 2, 1, 3); ctx.fillRect(5, 2, 1, 3); }
    ctx.setTransform(1, 0, 0, 1, 0, 0);
  }

  /* Flèches vers ce qui est hors écran et important. */
  function edgeArrow(wx, wy, col) {
    const sx = wx - camX, sy = wy - camY;
    if (sx > 0 && sx < VW && sy > 0 && sy < VH) return;
    const cx = VW / 2, cy = VH / 2;
    const a = Math.atan2(sy - cy, sx - cx);
    const k = Math.min((VW / 2 - 14) / Math.max(0.01, Math.abs(Math.cos(a))), (VH / 2 - 14) / Math.max(0.01, Math.abs(Math.sin(a))));
    const x = Math.round(cx + Math.cos(a) * k), y = Math.round(cy + Math.sin(a) * k);
    const blink = Math.floor(time * 6) % 2 === 0;
    ctx.fillStyle = blink ? col : '#ffffff';
    for (let i = 0; i < 5; i++) {
      ctx.fillRect(Math.round(x + Math.cos(a) * i), Math.round(y + Math.sin(a) * i), 2, 2);
      ctx.fillRect(Math.round(x + Math.cos(a + 2.5) * i), Math.round(y + Math.sin(a + 2.5) * i), 1, 1);
      ctx.fillRect(Math.round(x + Math.cos(a - 2.5) * i), Math.round(y + Math.sin(a - 2.5) * i), 1, 1);
    }
  }
  function drawIndicators() {
    if (!me) return;
    for (const e of enemies) {
      if (e.dead || !(e.boss || e.type === 'cargo')) continue;
      edgeArrow(e.x, e.y, e.boss ? '#ff4a4a' : '#ffd84a');
    }
    for (const s of players) if (s !== me) edgeArrow(s.x, s.y, s.dead ? '#6cf06c' : '#4ad6ff');
  }

  /* ---------- Boucle ---------- */
  function frame(dt, active) {
    frameT += dt;
    if (mode === 'guest' && me) {
      time += dt;
      Coop.guestFrame(dt, active);
    } else if (active && me) {
      accumulator += Math.min(dt, 0.1);
      const h = 1 / 60;
      let n = 0;
      while (accumulator >= h && n < 6) {
        step(h);
        accumulator -= h;
        n++;
        if (!me) break;
      }
    } else if (!me) {
      time += dt;
    }
    draw();
  }

  function isFlying() { return !!(me && run && !run.over); }

  function hudData() {
    if (!run || !me) return null;
    const st = me.st;
    const mate = players.find(s => s !== me);
    return {
      hull: Math.max(0, me.hull), maxHull: st.maxHull,
      shield: me.shield, maxShield: st.shield ? st.maxHull * st.shieldMul : 0,
      sector: run.sector, prog: clamp(run.t / run.dur, 0, 1),
      boss: bosses.length ? {
        name: bosses.map(b => b.def.name).join(' + '),
        hp: bosses.reduce((sum, b) => sum + Math.max(0, b.hp), 0),
        maxHp: bosses.reduce((sum, b) => sum + b.maxHp, 0) + (bosses.length === 1 && run.sector >= TWO_BOSS_SECTOR ? bosses[0].maxHp : 0),
      } : null,
      combo: run.combo, comboBonus: st.combo ? Math.min(st.comboMax, run.combo * 0.01) : 0,
      frenzy: Math.floor(me.frenzy),
      dash: st.dash, charges: me.charges, dashMax: st.dashCharges,
      dashProg: st.dash ? clamp(me.dashCd / st.dashCd, 0, 1) : 0,
      kills: run.kills, time: run.time, revives: me.revives,
      lowHull: !me.dead && me.hull < st.maxHull * 0.3,
      dead: me.dead,
      mate: mate ? { hull: Math.max(0, mate.hull), maxHull: mate.st.maxHull, dead: mate.dead, rescue: mate.rescue / mate.rescueNeed, rescueNeed: mate.rescueNeed } : null,
      rescue: me.rescue / me.rescueNeed,
      rescueNeed: me.rescueNeed,
    };
  }

  /* ---------- Clavier, souris, tactile ---------- */
  function bindInput() {
    window.addEventListener('keydown', e => {
      if (e.repeat) return;
      Input.keys[e.code] = true;
      if (['ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight', 'Space', 'Tab'].includes(e.code)) e.preventDefault();
      if (e.code === 'Space' || e.code === 'ShiftLeft' || e.code === 'ShiftRight') Input.dashQueued = true;
    });
    window.addEventListener('keyup', e => { Input.keys[e.code] = false; });
    window.addEventListener('blur', () => { Input.keys = {}; Input.stick = null; });

    const toLogical = ev => {
      const r = cv.getBoundingClientRect();
      return { x: ((ev.clientX - r.left) / r.width) * VW, y: ((ev.clientY - r.top) / r.height) * VH };
    };
    cv.addEventListener('pointermove', ev => {
      const at = toLogical(ev);
      if (ev.pointerType === 'mouse') {
        Input.mx = at.x; Input.my = at.y; Input.mouseSeen = true;
      } else if (Input.stick && Input.stick.id === ev.pointerId) {
        Input.stick.x = at.x; Input.stick.y = at.y;
      }
    });
    cv.addEventListener('pointerdown', ev => {
      if (ev.pointerType === 'mouse') return;
      if (!Input.stick) {
        const at = toLogical(ev);
        Input.stick = { id: ev.pointerId, ox: at.x, oy: at.y, x: at.x, y: at.y };
        try { cv.setPointerCapture(ev.pointerId); } catch (err) { /* pointeur déjà relâché */ }
      }
    });
    const release = ev => { if (Input.stick && Input.stick.id === ev.pointerId) Input.stick = null; };
    cv.addEventListener('pointerup', release);
    cv.addEventListener('pointercancel', release);
  }

  function queueDash() { Input.dashQueued = true; }
  function clearAll() {
    Music.stop();
    p = null; me = null; run = null; bosses = []; players = []; mode = 'solo'; droneList = [];
    enemies = []; pBullets = []; eBullets = []; missiles = []; mines = []; orbs = [];
    parts = []; rings = []; novas = []; bolts = []; texts = [];
    updateView();
  }

  /* Abandon volontaire : on garde les unités et on passe au bilan. */
  function abandon() {
    if (!run || run.over) return;
    endRun(true);
    clearAll();
  }

  return {
    init, start, startGuest, guestEnd, frame, step, draw, hudData, isFlying, onStatsChanged, setMateStats, removeMate,
    queueDash, abandon, clearAll, updateView, resize, Input, moveVector,
    get debug() { return { p: me, run, enemies, boss: bosses[0] || null, bosses, orbs, pBullets, eBullets, VW, VH, pixelScale, players, mode }; },
    /* Accès réservé à la synchronisation en ligne (coop.js). */
    net: {
      get players() { return players; }, get me() { return me; }, get run() { return run; }, get bosses() { return bosses; },
      set bosses(list) { bosses = list; },
      get enemies() { return enemies; }, get pBullets() { return pBullets; }, get eBullets() { return eBullets; },
      get missiles() { return missiles; }, get mines() { return mines; }, get orbs() { return orbs; }, get novas() { return novas; },
      get VW() { return VW; }, get VH() { return VH; }, get camX() { return camX; }, get camY() { return camY; },
      setActor, moveShip, orbitDrones, updateFx, burst, spark,
      addRemoteRing(x, y, r, c) { if (rings.length < 40) rings.push({ x, y, r: r * 0.2, max: r, c, t: 0 }); },
      addRemoteBolt(pts, t, color) { bolts.push({ pts, t, color }); },
      addRemoteText(x, y, s, c) { if (texts.length < 60) texts.push({ x, y, t: 0.55, s, c }); },
      addShake(v) { shake = Math.max(shake, v); },
    },
  };
})();
