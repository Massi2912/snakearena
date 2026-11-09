'use strict';

/* ==========================================================
   Snake Arena – Spiellogik
   1. Konstanten  2. Zustand  3. Schlangen  4. Futterpunkte
   5. KI          6. Kollision  7. Kamera & Zeichnen
   8. Eingabe     9. Oberfläche 10. Game Loop
   ========================================================== */

/* ---------- 1. Konstanten ---------- */
const WORLD_R = 2600;            // Radius des runden Spielfelds
const ORB_TARGET = 750;          // So viele Punkte liegen mindestens im Feld
const ORB_MAX = 3200;            // Obergrenze (Performance)
const BOT_COUNT = 14;            // Anzahl Computer-Schlangen
const START_SEGS = 20;           // Segmente einer neuen Schlange
const BASE_SPEED = 175;          // Tempo (Einheiten pro Sekunde)
const BOOST_SPEED = 330;         // Tempo mit Turbo
const TURN_RATE = 4.4;           // Max. Drehung pro Sekunde (rad)
const BOOST_DRAIN = 3.3;         // Punkte-Verlust pro Sekunde mit Turbo
const BOOST_MIN_SCORE = 4;       // Ab diesem Wert ist Turbo erlaubt
const SHIELD_TIME = 2;           // Schutz nach dem Start (Sekunden)
const BEST_KEY = 'snake-arena-best';
const NAME_KEY = 'snake-arena-name';
const COLOR_KEY = 'snake-arena-color';
const MENU_TEXT = 'Sammle Punkte und werde länger. Fährst du in den Körper einer anderen Schlange, bist du raus.';

// Farbpaare: [Hauptfarbe, helle Streifenfarbe]
const PALETTES = [
  ['#ff6b5b', '#ffa496'],
  ['#ffc83d', '#ffe28f'],
  ['#3ecf8e', '#82e8bb'],
  ['#2bc4d6', '#86dce8'],
  ['#4c8dff', '#92b6ff'],
  ['#9b6bff', '#c4a8ff'],
  ['#ff5fa2', '#ff9fc9'],
  ['#d7dde8', '#f3f5f9']
];

const BOT_NAMES = [
  'Lena', 'Noah', 'Mia', 'Elias', 'Emma', 'Finn', 'Sofia', 'Luca', 'Hanna', 'Ben',
  'Anna', 'Jonas', 'Lara', 'Paul', 'Nina', 'Max', 'Clara', 'Tim', 'Sara', 'Leo',
  'Greta', 'Felix', 'Ida', 'Moritz', 'Zoe', 'Emil'
];

/* ---------- 2. Zustand ---------- */
const canvas = document.getElementById('game');
const ctx = canvas.getContext('2d');

const world = { snakes: [], orbs: [], time: 0 };
let player = null;
let mode = 'menu';            // 'menu' | 'playing' | 'paused' | 'dead'
let nextId = 1;
let W = 0, H = 0, dpr = 1, remPx = 16;
const cam = { x: 0, y: 0, zoom: 1 };
let menuTarget = null;        // Schlange, der die Kamera im Menü folgt
let deathTimer = 0;
let lastKiller = null;        // Name des Verursachers (oder null = Rand)
let deadScore = 0, deadRank = 0, deadTotal = 0;

const pointer = { x: 0, y: 0, active: false };
const keys = { left: false, right: false, boost: false };
let mouseBoost = false;
let touchBoost = false;

/* ---------- Hilfsfunktionen ---------- */
const rand = (a, b) => a + Math.random() * (b - a);
const TAU = Math.PI * 2;

function angDiff(a, b) {
  let d = a - b;
  while (d > Math.PI) d -= TAU;
  while (d < -Math.PI) d += TAU;
  return d;
}

function loadStore(key, fallback) {
  try { const v = localStorage.getItem(key); return v === null ? fallback : v; }
  catch (e) { return fallback; }
}
function saveStore(key, value) {
  try { localStorage.setItem(key, String(value)); }
  catch (e) { /* nicht verfügbar – ignorieren */ }
}

/* ---------- 3. Schlangen ---------- */
function updateDims(s) {
  s.r = 8 + Math.min(12, Math.sqrt(Math.max(0, s.score)) * 0.9);
  s.spacing = s.r * 0.6;
  s.extent = s.segs.length * s.spacing + s.r * 2;
}

function targetSegs(s) {
  return START_SEGS + Math.floor(s.score);
}

function makeSnake(opts) {
  const s = {
    id: nextId++,
    name: opts.name,
    c1: opts.palette[0],
    c2: opts.palette[1],
    isPlayer: !!opts.isPlayer,
    alive: true,
    angle: opts.angle,
    targetAngle: opts.angle,
    score: opts.score || 0,
    segs: [],
    r: 10, spacing: 6, extent: 0,
    boosting: false,
    dropTimer: 0,
    shield: opts.isPlayer ? SHIELD_TIME : 1,
    thinkTimer: rand(0, 0.2),
    wander: opts.angle,
    aggro: Math.random() < 0.45,
    respawnAt: 0
  };
  updateDims(s);
  const n = targetSegs(s);

  // Körper als Spirale hinter dem Kopf legen und ins Feld klemmen.
  // So ragen auch lange Schlangen beim Start nie über den Rand hinaus.
  const limit = WORLD_R - 70;
  const turnSign = Math.random() < 0.5 ? 1 : -1;
  let px = opts.x, py = opts.y;
  let dir = opts.angle + Math.PI;
  for (let i = 0; i < n; i++) {
    s.segs.push({ x: px, y: py });
    const rad = 140 + i * s.spacing * 0.12;
    dir += turnSign * (s.spacing / rad);
    px += Math.cos(dir) * s.spacing;
    py += Math.sin(dir) * s.spacing;
    const dd = Math.sqrt(px * px + py * py);
    if (dd > limit) { px *= limit / dd; py *= limit / dd; }
  }
  updateDims(s);
  return s;
}

// Sucht einen freien Startpunkt, möglichst weit weg von anderen Schlangen
function findSpawn(avoidPlayerDist) {
  let best = null, bestScore = -1;
  for (let t = 0; t < 30; t++) {
    const a = rand(0, TAU);
    const d = Math.sqrt(Math.random()) * WORLD_R * 0.75;
    const x = Math.cos(a) * d, y = Math.sin(a) * d;
    let minD = Infinity;
    for (const o of world.snakes) {
      if (!o.alive) continue;
      for (let i = 0; i < o.segs.length; i += 4) {
        const dx = o.segs[i].x - x, dy = o.segs[i].y - y;
        const dd = Math.sqrt(dx * dx + dy * dy);
        if (dd < minD) minD = dd;
      }
    }
    if (avoidPlayerDist && player && player.alive) {
      const dx = player.segs[0].x - x, dy = player.segs[0].y - y;
      if (Math.sqrt(dx * dx + dy * dy) < avoidPlayerDist) continue;
    }
    if (minD > bestScore) { bestScore = minD; best = { x, y }; }
    if (minD > 450) break;
  }
  return best || { x: 0, y: 0 };
}

function spawnBot() {
  const pos = findSpawn(900);
  const big = Math.random() < 0.15;
  return makeSnake({
    name: BOT_NAMES[Math.floor(Math.random() * BOT_NAMES.length)],
    palette: PALETTES[Math.floor(Math.random() * PALETTES.length)],
    x: pos.x, y: pos.y, angle: rand(0, TAU),
    score: big ? rand(80, 260) : rand(0, 50)
  });
}

// Passt die Segmentanzahl an die Punkte an
function syncSegments(s) {
  updateDims(s);
  const n = targetSegs(s);
  while (s.segs.length < n) {
    const t = s.segs[s.segs.length - 1];
    s.segs.push({ x: t.x, y: t.y });
  }
  while (s.segs.length > n && s.segs.length > START_SEGS) s.segs.pop();
  updateDims(s);
}

function moveSnake(s, dt) {
  // Drehen (begrenzte Drehgeschwindigkeit)
  const diff = angDiff(s.targetAngle, s.angle);
  const maxTurn = TURN_RATE * dt * (s.boosting ? 0.85 : 1);
  s.angle += Math.max(-maxTurn, Math.min(maxTurn, diff));

  // Turbo kostet Punkte und lässt Futter fallen
  if (s.boosting && s.score <= BOOST_MIN_SCORE) s.boosting = false;
  if (s.boosting) {
    s.score = Math.max(0, s.score - BOOST_DRAIN * dt);
    s.dropTimer -= dt;
    if (s.dropTimer <= 0) {
      s.dropTimer = 0.3;
      const tail = s.segs[s.segs.length - 1];
      addOrb(tail.x, tail.y, 1, s.c1, s.id, world.time + 1.5);
    }
  }

  const speed = s.boosting ? BOOST_SPEED : BASE_SPEED;
  const head = s.segs[0];
  head.x += Math.cos(s.angle) * speed * dt;
  head.y += Math.sin(s.angle) * speed * dt;

  // Körper folgt dem Kopf mit festem Abstand
  const sp = s.spacing;
  for (let i = 1; i < s.segs.length; i++) {
    const p = s.segs[i - 1], q = s.segs[i];
    const dx = q.x - p.x, dy = q.y - p.y;
    const d = Math.sqrt(dx * dx + dy * dy);
    if (d > sp) {
      q.x = p.x + dx / d * sp;
      q.y = p.y + dy / d * sp;
    }
  }
  if (s.shield > 0) s.shield -= dt;
  syncSegments(s);
}

function killSnake(s, killer) {
  if (!s.alive) return;
  s.alive = false;
  s.respawnAt = world.time + 3;
  // Körper verwandelt sich in Futterpunkte
  const v = 1.2 + s.r / 12;
  for (let i = 0; i < s.segs.length; i += 2) {
    addOrb(s.segs[i].x + rand(-6, 6), s.segs[i].y + rand(-6, 6), v, Math.random() < 0.5 ? s.c1 : s.c2);
  }
  if (s.isPlayer) onPlayerDeath(killer);
}

/* ---------- 4. Futterpunkte ---------- */
function addOrb(x, y, v, color, from, blockUntil) {
  if (world.orbs.length >= ORB_MAX) return;
  world.orbs.push({
    x, y, v, c: color,
    r: Math.min(11, 3.5 + v * 1.6),
    ph: Math.random() * TAU,
    from: from || 0,
    block: blockUntil || 0
  });
}

function randomOrb() {
  const a = rand(0, TAU);
  const d = Math.sqrt(Math.random()) * (WORLD_R - 60);
  const roll = Math.random();
  const v = roll < 0.7 ? 1 : roll < 0.95 ? 2 : 4;
  const pal = PALETTES[Math.floor(Math.random() * PALETTES.length)];
  addOrb(Math.cos(a) * d, Math.sin(a) * d, v, pal[0]);
}

function updateEating(s, dt) {
  const head = s.segs[0];
  const mag = s.r * 2.6, mag2 = mag * mag;
  const eatR = s.r;
  const orbs = world.orbs;
  for (let i = orbs.length - 1; i >= 0; i--) {
    const o = orbs[i];
    if (o.from === s.id && world.time < o.block) continue;
    const dx = head.x - o.x, dy = head.y - o.y;
    const d2 = dx * dx + dy * dy;
    if (d2 > mag2) continue;
    const d = Math.sqrt(d2);
    if (d < eatR + o.r * 0.3) {
      s.score += o.v;
      orbs[i] = orbs[orbs.length - 1];
      orbs.pop();
      continue;
    }
    const pull = Math.min(d, 380 * dt);       // Punkte werden angesaugt
    o.x += dx / d * pull;
    o.y += dy / d * pull;
  }
}

/* ---------- 5. KI ---------- */
// Prüft, ob in Richtung ang Platz ist (Rand, andere Schlangen, eigener Körper)
function clearAhead(s, ang) {
  const h = s.segs[0];
  const cx = Math.cos(ang), cy = Math.sin(ang);
  const probes = [s.r * 2.5, s.r * 5, s.r * 9];
  for (const d of probes) {
    const px = h.x + cx * d, py = h.y + cy * d;
    if (px * px + py * py > (WORLD_R - 40) * (WORLD_R - 40)) return false;
    for (const b of world.snakes) {
      if (!b.alive || (b.shield > 0 && b !== s)) continue;
      const lim = (s.r + b.r) * 0.95, lim2 = lim * lim;
      const from = b === s ? 8 : 0;
      for (let i = from; i < b.segs.length; i++) {
        const dx = px - b.segs[i].x, dy = py - b.segs[i].y;
        if (dx * dx + dy * dy < lim2) return false;
      }
    }
  }
  return true;
}

function botThink(s) {
  const h = s.segs[0];
  let desired = s.wander;
  let target = null, prey = null;
  const dc = Math.sqrt(h.x * h.x + h.y * h.y);

  if (dc > WORLD_R - 380) {
    desired = Math.atan2(-h.y, -h.x);
  } else {
    if (s.aggro) {
      let bestD2 = 700 * 700;
      for (const o of world.snakes) {
        if (o === s || !o.alive || o.shield > 0) continue;
        if (o.score * 1.3 > s.score) continue;
        const dx = o.segs[0].x - h.x, dy = o.segs[0].y - h.y;
        const d2 = dx * dx + dy * dy;
        if (d2 < bestD2) { bestD2 = d2; prey = { o, d: Math.sqrt(d2) }; }
      }
    }
    if (prey) {
      const lead = Math.min(250, prey.d * 0.6);
      const ox = prey.o.segs[0].x + Math.cos(prey.o.angle) * lead;
      const oy = prey.o.segs[0].y + Math.sin(prey.o.angle) * lead;
      desired = Math.atan2(oy - h.y, ox - h.x);
    } else {
      let bestVal = 0;
      for (const o of world.orbs) {
        const dx = o.x - h.x, dy = o.y - h.y;
        const d2 = dx * dx + dy * dy;
        if (d2 > 480 * 480) continue;
        const val = o.v / (Math.sqrt(d2) + 80);
        if (val > bestVal) { bestVal = val; target = o; }
      }
      if (target) desired = Math.atan2(target.y - h.y, target.x - h.x);
      else if (Math.random() < 0.25) { s.wander += rand(-0.9, 0.9); desired = s.wander; }
    }
  }

  // Hindernissen ausweichen
  const offsets = [0, 0.35, -0.35, 0.7, -0.7, 1.1, -1.1, 1.6, -1.6];
  let chosen = null;
  for (const off of offsets) {
    if (clearAhead(s, desired + off)) { chosen = desired + off; break; }
  }
  if (chosen === null) chosen = desired + (Math.random() < 0.5 ? 1.6 : -1.6);
  s.targetAngle = chosen;
  if (!target && !prey) s.wander = chosen;

  // Turbo nur beim Jagen
  s.boosting = !!prey && prey.d < 400 && s.score > BOOST_MIN_SCORE + 12;
}

/* ---------- 6. Kollision ---------- */
function checkCollisions() {
  for (const a of world.snakes) {
    if (!a.alive || a.shield > 0) continue;
    const h = a.segs[0];
    const lim0 = WORLD_R - a.r * 0.3;
    if (h.x * h.x + h.y * h.y > lim0 * lim0) {
      killSnake(a, null);
      continue;
    }
    for (const b of world.snakes) {
      if (b === a || !b.alive || b.shield > 0) continue;
      const ex = b.extent + a.r;
      const hx = h.x - b.segs[0].x, hy = h.y - b.segs[0].y;
      if (hx * hx + hy * hy > ex * ex) continue;
      const lim = (a.r + b.r) * 0.7, lim2 = lim * lim;
      let hit = false;
      for (let i = 1; i < b.segs.length; i++) {
        const dx = h.x - b.segs[i].x, dy = h.y - b.segs[i].y;
        if (dx * dx + dy * dy < lim2) { hit = true; break; }
      }
      if (hit) { killSnake(a, b); break; }
    }
  }
}

/* ---------- Update ---------- */
function update(dt) {
  world.time += dt;

  // Eingabe der Spielerin / des Spielers
  if (player && player.alive) {
    const turn = (keys.right ? 1 : 0) - (keys.left ? 1 : 0);
    if (turn) player.targetAngle = player.angle + turn;
    else if (pointer.active) player.targetAngle = Math.atan2(pointer.y - H / 2, pointer.x - W / 2);
    player.boosting = (mouseBoost || keys.boost || touchBoost) && player.score > BOOST_MIN_SCORE;
  }

  // KI denkt in Abständen
  for (const s of world.snakes) {
    if (!s.alive || s.isPlayer) continue;
    s.thinkTimer -= dt;
    if (s.thinkTimer <= 0) {
      s.thinkTimer = 0.1 + Math.random() * 0.1;
      botThink(s);
    }
  }

  for (const s of world.snakes) {
    if (!s.alive) continue;
    moveSnake(s, dt);
    updateEating(s, dt);
  }

  checkCollisions();

  // Computer-Schlangen neu starten
  for (let i = 0; i < world.snakes.length; i++) {
    const s = world.snakes[i];
    if (!s.alive && !s.isPlayer && world.time >= s.respawnAt) world.snakes[i] = spawnBot();
  }

  // Futter nachfüllen
  let guard = 0;
  while (world.orbs.length < ORB_TARGET && guard++ < 10) randomOrb();

  if (mode === 'dead' && deathTimer > 0) {
    deathTimer -= dt;
    if (deathTimer <= 0) showGameOver();
  }
}

/* ---------- 7. Kamera & Zeichnen ---------- */
function baseScale() { return Math.min(W, H) / 620; }

function updateCamera(dt) {
  let tx = cam.x, ty = cam.y, zt = 1;
  if (player && player.alive) {
    tx = player.segs[0].x; ty = player.segs[0].y;
    zt = 1 / (1 + Math.min(320, player.score) / 420);
  } else if (mode === 'menu') {
    if (!menuTarget || !menuTarget.alive) {
      const alive = world.snakes.filter((s) => s.alive);
      menuTarget = alive.sort((a, b) => b.score - a.score)[0] || null;
    }
    if (menuTarget) { tx = menuTarget.segs[0].x; ty = menuTarget.segs[0].y; }
    zt = 0.9;
  } else {
    zt = cam.zoom;
  }
  const k = Math.min(1, dt * 8);
  cam.x += (tx - cam.x) * k;
  cam.y += (ty - cam.y) * k;
  cam.zoom += (zt - cam.zoom) * Math.min(1, dt * 2);
}

function render() {
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.fillStyle = '#05070b';
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  const sc = baseScale() * cam.zoom;
  ctx.setTransform(dpr * sc, 0, 0, dpr * sc, dpr * (W / 2 - cam.x * sc), dpr * (H / 2 - cam.y * sc));
  const vw = W / sc / 2 + 80, vh = H / sc / 2 + 80;
  const minX = cam.x - vw, maxX = cam.x + vw, minY = cam.y - vh, maxY = cam.y + vh;

  // Spielfeld
  ctx.fillStyle = '#0f1420';
  ctx.beginPath();
  ctx.arc(0, 0, WORLD_R, 0, TAU);
  ctx.fill();

  // Punktraster
  const G = 80;
  ctx.fillStyle = 'rgba(255, 255, 255, 0.055)';
  for (let x = Math.floor(minX / G) * G; x <= maxX; x += G) {
    for (let y = Math.floor(minY / G) * G; y <= maxY; y += G) {
      if (x * x + y * y < (WORLD_R - 20) * (WORLD_R - 20)) ctx.fillRect(x - 1.5, y - 1.5, 3, 3);
    }
  }

  // Rand
  ctx.strokeStyle = '#c0392b';
  ctx.lineWidth = 16;
  ctx.beginPath();
  ctx.arc(0, 0, WORLD_R + 8, 0, TAU);
  ctx.stroke();

  // Futterpunkte
  const t = world.time;
  for (const o of world.orbs) {
    if (o.x < minX || o.x > maxX || o.y < minY || o.y > maxY) continue;
    const r = o.r * (1 + 0.12 * Math.sin(t * 3 + o.ph));
    ctx.fillStyle = o.c;
    ctx.globalAlpha = 0.2;
    ctx.beginPath(); ctx.arc(o.x, o.y, r * 1.9, 0, TAU); ctx.fill();
    ctx.globalAlpha = 1;
    ctx.beginPath(); ctx.arc(o.x, o.y, r, 0, TAU); ctx.fill();
  }

  // Schlangen: Computer zuerst, Spielerin / Spieler obendrauf
  for (const s of world.snakes) if (s.alive && !s.isPlayer) drawSnake(s, minX, maxX, minY, maxY);
  if (player && player.alive) drawSnake(player, minX, maxX, minY, maxY);

  drawMinimap();
}

function drawSnake(s, minX, maxX, minY, maxY) {
  const n = s.segs.length, r = s.r;
  const blink = s.shield > 0 && Math.floor(world.time * 8) % 2 === 0;
  ctx.globalAlpha = blink ? 0.5 : 1;
  ctx.strokeStyle = 'rgba(0, 0, 0, 0.28)';
  ctx.lineWidth = 1.5;

  for (let i = n - 1; i >= 1; i--) {
    const p = s.segs[i];
    if (p.x < minX - r || p.x > maxX + r || p.y < minY - r || p.y > maxY + r) continue;
    const tt = i / n;
    const rr = r * (tt > 0.7 ? 1 - (tt - 0.7) : 1);
    ctx.fillStyle = Math.floor(i / 3) % 2 ? s.c2 : s.c1;
    ctx.beginPath();
    ctx.arc(p.x, p.y, rr, 0, TAU);
    ctx.fill();
    ctx.stroke();
  }

  // Kopf mit Augen
  const h = s.segs[0];
  ctx.fillStyle = s.c1;
  ctx.beginPath();
  ctx.arc(h.x, h.y, r * 1.05, 0, TAU);
  ctx.fill();
  ctx.stroke();
  const cx = Math.cos(s.angle), cy = Math.sin(s.angle);
  for (const side of [-1, 1]) {
    const ex = h.x + cx * r * 0.35 - cy * r * 0.5 * side;
    const ey = h.y + cy * r * 0.35 + cx * r * 0.5 * side;
    ctx.fillStyle = '#ffffff';
    ctx.beginPath(); ctx.arc(ex, ey, r * 0.34, 0, TAU); ctx.fill();
    ctx.fillStyle = '#10131c';
    ctx.beginPath(); ctx.arc(ex + cx * r * 0.12, ey + cy * r * 0.12, r * 0.17, 0, TAU); ctx.fill();
  }
  ctx.globalAlpha = 1;

  if (!s.isPlayer) {
    ctx.fillStyle = 'rgba(230, 234, 245, 0.85)';
    ctx.font = '600 13px system-ui, sans-serif';
    ctx.textAlign = 'center';
    ctx.fillText(s.name, h.x, h.y - r - 10);
  }
}

// Minimap: Arena, Körper aller Schlangen, grosse Futterhaufen, eigener Pfeil
function drawMinimap() {
  if (mode === 'menu') return;
  const touch = document.body.classList.contains('touch');
  const rad = remPx * (touch ? 5.2 : 6.4);
  const mx = W - rad - remPx;
  const my = H - rad - remPx * (touch ? 7.8 : 1);
  const k = rad / (WORLD_R + 80);
  const X = (x) => mx + x * k;
  const Y = (y) => my + y * k;

  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.save();
  ctx.beginPath();
  ctx.arc(mx, my, rad, 0, TAU);
  ctx.fillStyle = 'rgba(8, 11, 18, 0.82)';
  ctx.fill();
  ctx.clip();

  // Arena mit rotem Rand wie im Spiel
  ctx.beginPath();
  ctx.arc(mx, my, WORLD_R * k, 0, TAU);
  ctx.fillStyle = '#0f1420';
  ctx.fill();
  ctx.strokeStyle = '#c0392b';
  ctx.lineWidth = 1.5;
  ctx.stroke();

  // Grössere Futterpunkte (z. B. Reste gestorbener Schlangen)
  ctx.fillStyle = 'rgba(255, 255, 255, 0.35)';
  for (const o of world.orbs) {
    if (o.v >= 2) ctx.fillRect(X(o.x) - 0.6, Y(o.y) - 0.6, 1.4, 1.4);
  }

  // Körper der Schlangen
  ctx.lineCap = 'round';
  ctx.lineJoin = 'round';
  const bodyLine = (s, alpha, width) => {
    ctx.globalAlpha = alpha;
    ctx.strokeStyle = s.c1;
    ctx.lineWidth = width;
    ctx.beginPath();
    ctx.moveTo(X(s.segs[0].x), Y(s.segs[0].y));
    for (let i = 5; i < s.segs.length; i += 5) ctx.lineTo(X(s.segs[i].x), Y(s.segs[i].y));
    ctx.stroke();
    ctx.globalAlpha = 1;
  };
  for (const s of world.snakes) {
    if (!s.alive || s.isPlayer) continue;
    bodyLine(s, 0.55, Math.min(3, 1.2 + s.r * 0.07));
  }
  if (player && player.alive) bodyLine(player, 0.9, 2.4);

  // Köpfe der Computer-Schlangen; Ring = deutlich grösser als du
  for (const s of world.snakes) {
    if (!s.alive || s.isPlayer) continue;
    const hx = X(s.segs[0].x), hy = Y(s.segs[0].y);
    const hr = 2 + Math.min(2, s.score / 150);
    ctx.fillStyle = s.c1;
    ctx.beginPath(); ctx.arc(hx, hy, hr, 0, TAU); ctx.fill();
    if (player && player.alive && s.score > player.score * 1.3 + 5) {
      ctx.strokeStyle = 'rgba(255, 255, 255, 0.85)';
      ctx.lineWidth = 1;
      ctx.beginPath(); ctx.arc(hx, hy, hr + 2, 0, TAU); ctx.stroke();
    }
  }

  // Eigene Position: Pfeil in Blickrichtung (Computer-Schlangen sind Kreise)
  if (player && player.alive) {
    const hx = X(player.segs[0].x), hy = Y(player.segs[0].y);
    const a = player.angle;
    const tip = 7, back = 4.5, wing = 4.2;
    ctx.beginPath();
    ctx.moveTo(hx + Math.cos(a) * tip, hy + Math.sin(a) * tip);
    ctx.lineTo(hx + Math.cos(a + 2.5) * wing, hy + Math.sin(a + 2.5) * wing);
    ctx.lineTo(hx - Math.cos(a) * back * 0.4, hy - Math.sin(a) * back * 0.4);
    ctx.lineTo(hx + Math.cos(a - 2.5) * wing, hy + Math.sin(a - 2.5) * wing);
    ctx.closePath();
    ctx.fillStyle = player.c1;
    ctx.fill();
    ctx.strokeStyle = '#0b0f17';
    ctx.lineWidth = 1.5;
    ctx.lineJoin = 'round';
    ctx.stroke();

    ctx.fillStyle = 'rgba(230, 234, 245, 0.9)';
    ctx.font = '600 ' + Math.round(remPx * 0.62) + 'px system-ui, sans-serif';
    ctx.textAlign = 'center';
    ctx.fillText('Du', hx, hy - 10);
  }
  ctx.restore();

  // Aussenrand der Minimap
  ctx.strokeStyle = '#2a344b';
  ctx.lineWidth = 1.5;
  ctx.beginPath();
  ctx.arc(mx, my, rad, 0, TAU);
  ctx.stroke();
}

/* ---------- 8. Eingabe ---------- */
canvas.addEventListener('pointermove', (e) => {
  pointer.x = e.clientX; pointer.y = e.clientY; pointer.active = true;
});
canvas.addEventListener('pointerdown', (e) => {
  pointer.x = e.clientX; pointer.y = e.clientY; pointer.active = true;
  if (e.pointerType === 'mouse' && e.button === 0) mouseBoost = true;
});
window.addEventListener('pointerup', (e) => {
  if (e.pointerType === 'mouse') mouseBoost = false;
});
window.addEventListener('blur', () => { mouseBoost = false; touchBoost = false; keys.left = keys.right = keys.boost = false; });

const boostBtn = document.getElementById('boost-btn');
boostBtn.addEventListener('pointerdown', (e) => {
  e.preventDefault();
  touchBoost = true;
  boostBtn.classList.add('down');
  boostBtn.setPointerCapture(e.pointerId);
});
const endBoost = () => { touchBoost = false; boostBtn.classList.remove('down'); };
boostBtn.addEventListener('pointerup', endBoost);
boostBtn.addEventListener('pointercancel', endBoost);

function setKey(e, down) {
  switch (e.key) {
    case 'ArrowLeft': case 'a': case 'A': keys.left = down; break;
    case 'ArrowRight': case 'd': case 'D': keys.right = down; break;
    case ' ': case 'Shift': keys.boost = down; break;
    default: return false;
  }
  return true;
}

document.addEventListener('keydown', (e) => {
  if (e.target && e.target.tagName === 'INPUT') {
    if (e.key === 'Enter') { e.preventDefault(); startGame(); }
    return;
  }
  if (e.key === 'Enter') {
    e.preventDefault();
    if (mode === 'menu' || mode === 'dead') startGame();
    else if (mode === 'paused') togglePause();
    return;
  }
  if (e.key === 'Escape' || e.key === 'p' || e.key === 'P') {
    e.preventDefault();
    if (!e.repeat) togglePause();
    return;
  }
  if (setKey(e, true)) e.preventDefault();
});
document.addEventListener('keyup', (e) => { setKey(e, false); });

document.addEventListener('visibilitychange', () => {
  if (document.hidden && mode === 'playing') togglePause();
});

/* ---------- 9. Oberfläche ---------- */
const el = {
  overlay: document.getElementById('overlay'),
  title: document.getElementById('ov-title'),
  text: document.getElementById('ov-text'),
  result: document.getElementById('result'),
  resScore: document.getElementById('res-score'),
  resRank: document.getElementById('res-rank'),
  resCause: document.getElementById('res-cause'),
  name: document.getElementById('name'),
  swatches: document.getElementById('swatches'),
  preview: document.getElementById('preview'),
  play: document.getElementById('play'),
  best: document.getElementById('best'),
  hud: document.getElementById('hud'),
  score: document.getElementById('score'),
  rank: document.getElementById('rank'),
  board: document.getElementById('board'),
  boardList: document.getElementById('board-list'),
  legend: document.getElementById('legend'),
  pauseBtn: document.getElementById('pause-btn'),
  pause: document.getElementById('pause'),
  pauseInfo: document.getElementById('pause-info'),
  resume: document.getElementById('resume'),
  restart: document.getElementById('restart'),
  toMenu: document.getElementById('to-menu')
};

if (window.matchMedia('(hover: none) and (pointer: coarse)').matches) {
  document.body.classList.add('touch');
}

let selectedColor = Math.max(0, Math.min(PALETTES.length - 1, parseInt(loadStore(COLOR_KEY, '0'), 10) || 0));
let best = parseInt(loadStore(BEST_KEY, '0'), 10) || 0;
el.name.value = loadStore(NAME_KEY, '');

// Vorschau der gewählten Schlange im Startmenü
function drawPreview() {
  const cv = el.preview, c = cv.getContext('2d');
  const w = cv.width, h = cv.height;
  const pal = PALETTES[selectedColor];
  c.clearRect(0, 0, w, h);
  const n = 30, r = h * 0.17, step = w * 0.8 / n;
  const pts = [];
  for (let i = 0; i < n; i++) {
    pts.push({ x: w * 0.9 - i * step, y: h / 2 + Math.sin(i * 0.38 + 0.6) * h * 0.2 });
  }
  c.strokeStyle = 'rgba(0, 0, 0, 0.3)';
  c.lineWidth = 2;
  for (let i = n - 1; i >= 1; i--) {
    const tt = i / n;
    const rr = r * (tt > 0.7 ? 1 - (tt - 0.7) : 1);
    c.fillStyle = Math.floor(i / 3) % 2 ? pal[1] : pal[0];
    c.beginPath(); c.arc(pts[i].x, pts[i].y, rr, 0, TAU); c.fill(); c.stroke();
  }
  const hd = pts[0];
  c.fillStyle = pal[0];
  c.beginPath(); c.arc(hd.x, hd.y, r * 1.05, 0, TAU); c.fill(); c.stroke();
  const ang = Math.atan2(pts[0].y - pts[1].y, pts[0].x - pts[1].x);
  const cx = Math.cos(ang), cy = Math.sin(ang);
  for (const side of [-1, 1]) {
    const ex = hd.x + cx * r * 0.35 - cy * r * 0.5 * side;
    const ey = hd.y + cy * r * 0.35 + cx * r * 0.5 * side;
    c.fillStyle = '#ffffff';
    c.beginPath(); c.arc(ex, ey, r * 0.34, 0, TAU); c.fill();
    c.fillStyle = '#10131c';
    c.beginPath(); c.arc(ex + cx * r * 0.12, ey + cy * r * 0.12, r * 0.17, 0, TAU); c.fill();
  }
}

// Akzentfarbe der Oberfläche = Farbe der gewählten Schlange
function applyAccent() {
  document.documentElement.style.setProperty('--accent', PALETTES[selectedColor][0]);
}

function buildSwatches() {
  PALETTES.forEach((pal, i) => {
    const b = document.createElement('button');
    b.type = 'button';
    b.className = 'swatch' + (i === selectedColor ? ' on' : '');
    b.style.background = 'linear-gradient(135deg, ' + pal[0] + ' 50%, ' + pal[1] + ' 50%)';
    b.setAttribute('role', 'radio');
    b.setAttribute('aria-checked', String(i === selectedColor));
    b.setAttribute('aria-label', 'Farbe ' + (i + 1));
    b.addEventListener('click', () => {
      selectedColor = i;
      saveStore(COLOR_KEY, i);
      el.swatches.querySelectorAll('.swatch').forEach((x, j) => {
        x.classList.toggle('on', j === i);
        x.setAttribute('aria-checked', String(j === i));
      });
      applyAccent();
      drawPreview();
    });
    el.swatches.appendChild(b);
  });
}

const pts = (s) => Math.round(s.score * 10);

function updateBestText() {
  el.best.textContent = best > 0 ? 'Bestwert: ' + best + ' Punkte' : '';
}

function hideGameUi() {
  el.hud.hidden = true;
  el.board.hidden = true;
  el.legend.hidden = true;
  el.pauseBtn.hidden = true;
  boostBtn.hidden = true;
}

function showMenu() {
  el.title.textContent = 'Snake Arena';
  el.text.textContent = MENU_TEXT;
  el.result.hidden = true;
  el.play.textContent = 'Spielen';
  updateBestText();
  el.pause.hidden = true;
  el.overlay.hidden = false;
  hideGameUi();
}

function showGameOver() {
  el.title.textContent = 'Game Over';
  el.text.textContent = 'Du kannst direkt eine neue Runde starten.';
  el.resScore.textContent = deadScore;
  el.resRank.textContent = deadRank + ' von ' + deadTotal;
  el.resCause.textContent = lastKiller ? 'In ' + lastKiller + ' hineingefahren' : 'Rand berührt';
  el.result.hidden = false;
  el.play.textContent = 'Nochmal';
  updateBestText();
  el.overlay.hidden = false;
  hideGameUi();
}

function onPlayerDeath(killer) {
  mode = 'dead';
  lastKiller = killer ? killer.name : null;
  deadScore = pts(player);
  const list = world.snakes.filter((s) => s.alive).concat([player]).sort((a, b) => b.score - a.score);
  deadRank = list.indexOf(player) + 1;
  deadTotal = list.length;
  if (deadScore > best) { best = deadScore; saveStore(BEST_KEY, best); }
  deathTimer = 0.9;
  mouseBoost = false; touchBoost = false; keys.boost = false;
  el.pauseBtn.hidden = true;
}

// Neue Runde beginnen (auch aus dem Pausenmenü heraus)
function beginRun() {
  const name = el.name.value.trim().slice(0, 14) || 'Du';
  saveStore(NAME_KEY, el.name.value.trim());
  if (player) world.snakes = world.snakes.filter((s) => s !== player);
  const pos = findSpawn(0);
  player = makeSnake({
    name, palette: PALETTES[selectedColor],
    x: pos.x, y: pos.y, angle: rand(0, TAU), isPlayer: true, score: 0
  });
  world.snakes.push(player);
  cam.x = pos.x; cam.y = pos.y; cam.zoom = 1;
  mode = 'playing';
  lastScoreShown = -1;
  el.overlay.hidden = true;
  el.pause.hidden = true;
  el.hud.hidden = false;
  el.board.hidden = false;
  el.legend.hidden = false;
  el.pauseBtn.hidden = false;
  boostBtn.hidden = false;
  el.name.blur();
  boardTimer = 0;
}

function startGame() {
  if (mode === 'playing' || mode === 'paused') return;
  beginRun();
}

function updatePauseInfo() {
  const list = world.snakes.filter((s) => s.alive).sort((a, b) => b.score - a.score);
  const idx = list.indexOf(player);
  el.pauseInfo.textContent = 'Punkte: ' + pts(player) + (idx >= 0 ? ' · Platz ' + (idx + 1) + ' von ' + list.length : '');
}

function togglePause() {
  if (mode === 'playing') {
    mode = 'paused';
    mouseBoost = false; touchBoost = false;
    keys.left = keys.right = keys.boost = false;
    endBoost();
    updatePauseInfo();
    el.pause.hidden = false;
    el.pauseBtn.hidden = true;
    el.resume.focus({ preventScroll: true });
  } else if (mode === 'paused') {
    mode = 'playing';
    el.pause.hidden = true;
    el.pauseBtn.hidden = false;
    if (document.activeElement && document.activeElement.blur) document.activeElement.blur();
  }
}

function toMainMenu() {
  if (player) world.snakes = world.snakes.filter((s) => s !== player);
  player = null;
  menuTarget = null;
  mode = 'menu';
  showMenu();
}

el.play.addEventListener('click', () => { startGame(); el.play.blur(); });
el.pauseBtn.addEventListener('click', () => { togglePause(); el.pauseBtn.blur(); });
el.resume.addEventListener('click', () => { togglePause(); el.resume.blur(); });
el.restart.addEventListener('click', () => { beginRun(); el.restart.blur(); });
el.toMenu.addEventListener('click', () => { toMainMenu(); el.toMenu.blur(); });

// Rangliste und Anzeige
let boardTimer = 0;
let lastScoreShown = -1;
function updateHud(dt) {
  if (player && player.alive) {
    const p = pts(player);
    if (p !== lastScoreShown) { el.score.textContent = p; lastScoreShown = p; }
  }
  boardTimer -= dt;
  if (boardTimer > 0) return;
  boardTimer = 0.25;

  const list = world.snakes.filter((s) => s.alive).sort((a, b) => b.score - a.score);
  const top = list.slice(0, 5);
  el.boardList.textContent = '';
  const addRow = (rank, s) => {
    const li = document.createElement('li');
    if (s === player) li.className = 'me';
    const nm = document.createElement('span');
    nm.className = 'nm';
    nm.textContent = rank + '. ' + s.name;
    const pt = document.createElement('span');
    pt.className = 'pt';
    pt.textContent = pts(s);
    li.append(nm, pt);
    el.boardList.appendChild(li);
  };
  top.forEach((s, i) => addRow(i + 1, s));
  if (player && player.alive) {
    const idx = list.indexOf(player);
    if (idx >= 5) addRow(idx + 1, player);
    el.rank.textContent = 'Platz ' + (idx + 1) + ' von ' + list.length;
  }
}

/* ---------- 10. Game Loop ---------- */
function resize() {
  W = window.innerWidth;
  H = window.innerHeight;
  dpr = Math.min(window.devicePixelRatio || 1, 2);
  remPx = parseFloat(getComputedStyle(document.documentElement).fontSize) || 16;
  canvas.width = Math.round(W * dpr);
  canvas.height = Math.round(H * dpr);
}
window.addEventListener('resize', resize);

let lastTime = 0;
function frame(time) {
  const dt = Math.min((time - lastTime) / 1000, 0.05);
  lastTime = time;

  if (mode !== 'paused') {
    update(dt);
    updateCamera(dt);
  }
  updateHud(dt);
  render();
  requestAnimationFrame(frame);
}

// Start
resize();
buildSwatches();
applyAccent();
drawPreview();
for (let i = 0; i < BOT_COUNT; i++) world.snakes.push(spawnBot());
for (let i = 0; i < ORB_TARGET; i++) randomOrb();
// Die Computer-Schlangen vorlaufen lassen, damit das Feld belebt wirkt
for (let i = 0; i < 60; i++) update(0.05);
showMenu();
requestAnimationFrame((t) => { lastTime = t; frame(t); });