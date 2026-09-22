"use strict";

/* ============================================================
   DEFENCE LINE - a cartoon arcade game
   Plain HTML + CSS + vanilla JavaScript. No libraries, no backend.
   ============================================================ */

/* ---------- SETTINGS (safe to tweak) ---------- */
const CONFIG = {
  TARGET_IMAGE: "target.jpg",  // <- replace this file (or this path) to change the target photo
  PASSWORD_HASH: "eadc4464595dfd4157dc3f5ff7ccda0383cb334c7fc314599ca51a1ca23485ff", // SHA-256 of the lowercase password
  TARGET_COUNT: 4,             // exactly 4 targets - nothing ever spawns after the start
  FIRE_INTERVAL: 0.27,         // seconds between shots while the screen is held down
  TAP_COOLDOWN: 0.09,          // minimum seconds between tap-triggered shots
  BULLET_SPEED: 860,           // px per second (on a 740px tall screen)
  HITBOX: 0.47,                // hit area as a share of the photo size, for the first three targets
  NORMAL_SPEED: [19, 33],      // px/s downward for the first three targets
  FINAL_SPEED: 560,            // px/s downward once only one target is left - a huge jump from the normal speeds
  FINAL_DRIFT: [380, 620],     // px/s sideways bursts for the last target
  FINAL_SPAN: [0.08, 0.16],    // seconds between the last target's direction changes - rapid, twitchy, hard to read
  FINAL_EASE: 20,              // how instantly it snaps to a new direction (higher = snappier/less predictable)
  FINAL_SCALE: 0.34,           // the last target shrinks a lot - smaller AND much harder to land a shot on
  FINAL_HITBOX: 0.10,          // much tighter hit tolerance just for the last target - near-dead-center shots only
  FINAL_MIN_TIME: 0.65,        // bare-minimum safety net only (typical remaining distance is ~310-505px, so this rarely binds)
  SOUND: true                  // tiny built-in beeps (false = silent)
};

/* ---------- helpers ---------- */
const TAU = Math.PI * 2;
const FONT = '"sans-serif-condensed", "Roboto Condensed", "Arial Narrow", "Helvetica Neue", Arial, sans-serif';
const HIT_TIME = 0.34;                       // seconds a shot target lingers before it is removed
const JIT6 = [1, 0.75, 1, 0.75, 1, 0.75];   // spike shape for the muzzle flash
const CALM = !!(window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches);
const rand = (a, b) => a + Math.random() * (b - a);
const pick = a => a[(Math.random() * a.length) | 0];
const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, v));
const easeOutBack = x => 1 + 2.70158 * Math.pow(x - 1, 3) + 1.70158 * Math.pow(x - 1, 2);
function shuffle(a) {
  for (let i = a.length - 1; i > 0; i--) {
    const j = (Math.random() * (i + 1)) | 0;
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

/* SHA-256, so the password is never sitting in the code as plain text */
function sha256(text) {
  const rotr = (x, n) => (x >>> n) | (x << (32 - n));
  const K = [], h = [];
  for (let c = 0, p = 2; c < 64; p++) {
    let prime = true;
    for (let d = 2; d * d <= p; d++) if (p % d === 0) { prime = false; break; }
    if (!prime) continue;
    if (c < 8) h[c] = (Math.pow(p, 0.5) * 4294967296) | 0;
    K[c++] = (Math.pow(p, 1 / 3) * 4294967296) | 0;
  }
  const bytes = Array.from(new TextEncoder().encode(text));
  const bits = bytes.length * 8;
  bytes.push(0x80);
  while (bytes.length % 64 !== 56) bytes.push(0);
  for (let i = 7; i >= 0; i--) bytes.push(i > 3 ? 0 : (bits >>> (i * 8)) & 255);
  for (let o = 0; o < bytes.length; o += 64) {
    const w = [];
    for (let i = 0; i < 16; i++) {
      w[i] = (bytes[o + 4 * i] << 24) | (bytes[o + 4 * i + 1] << 16) | (bytes[o + 4 * i + 2] << 8) | bytes[o + 4 * i + 3];
    }
    for (let i = 16; i < 64; i++) {
      const s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >>> 3);
      const s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >>> 10);
      w[i] = (w[i - 16] + s0 + w[i - 7] + s1) | 0;
    }
    let [a, b, c, d, e, f, g, k] = h;
    for (let i = 0; i < 64; i++) {
      const t1 = (k + (rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)) + ((e & f) ^ (~e & g)) + K[i] + w[i]) | 0;
      const t2 = ((rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)) + ((a & b) ^ (a & c) ^ (b & c))) | 0;
      k = g; g = f; f = e; e = (d + t1) | 0; d = c; c = b; b = a; a = (t1 + t2) | 0;
    }
    [a, b, c, d, e, f, g, k].forEach((v, i) => { h[i] = (h[i] + v) | 0; });
  }
  return h.map(v => (v >>> 0).toString(16).padStart(8, "0")).join("");
}

/* ---------- DOM + target photo ---------- */
const $ = id => document.getElementById(id);
const canvas = $("stage"), ctx = canvas.getContext("2d");
const gameEl = $("game"), lockEl = $("lock"), introEl = $("intro"), endEl = $("end");
const pwInput = $("pw"), pwToggle = $("pwToggle"), pwError = $("pwError"), unlockBtn = $("unlockBtn");
const endTitle = $("endTitle"), endSub = $("endSub"), toastEl = $("toast");
const playBtn = $("playBtn"), replayBtn = $("replayBtn");

const photo = new Image();
let photoReady = false;
photo.onload = () => { photoReady = photo.naturalWidth > 0; };
photo.onerror = () => { photoReady = false; };      // a simple silhouette is drawn instead
photo.src = CONFIG.TARGET_IMAGE;

/* ---------- game state ---------- */
let W = 360, H = 640, DPR = 1, S = 1, Hs = 1, Ws = 1, LINE_Y = 480;
let state = "intro";                 // intro -> playing -> winning -> over (replay goes back to playing)
let time = 0, last = 0, raf = 0, fireT = 0, tapT = -1, endTimer = 0, overAt = 0;
let shake = 0, flash = 0, breached = false;
const targets = [], bullets = [], fx = [];
const cannon = { x: 180, y: 600, angle: 0, recoil: 0 };
const pointer = { has: false, down: false, mouse: false, x: 0, y: 0 };
const bg = document.createElement("canvas");

/* ---------- layout (responsive) ---------- */
function layout() {
  const box = gameEl.getBoundingClientRect();
  const nw = Math.max(240, Math.round(box.width));
  const nh = Math.max(320, Math.round(box.height));
  const kx = nw / W, ky = nh / H, first = !layout.ran;
  layout.ran = true;
  W = nw; H = nh;
  DPR = Math.min(window.devicePixelRatio || 1, 2.5);
  canvas.width = Math.round(W * DPR);
  canvas.height = Math.round(H * DPR);
  S = clamp(Math.min(W / 360, H / 740), 0.72, 1.5);
  Hs = H / 740;
  Ws = W / 360;
  LINE_Y = Math.round(H - clamp(H * 0.165, 98, 150));
  cannon.y = H - 44 * S;
  if (first) {
    cannon.x = W / 2;
  } else {
    cannon.x *= kx;
    for (const t of targets) { t.x *= kx; t.y *= ky; t.w = 74 * S * t.sc; t.h = 84 * S * t.sc; }
    for (const b of bullets) { b.x *= kx; b.y *= ky; b.r = 5.5 * S; }
    fx.length = 0;
  }
  buildBackground();
  if (!raf) render();
}

function buildBackground() {
  bg.width = canvas.width;
  bg.height = canvas.height;
  const g = bg.getContext("2d");
  g.setTransform(DPR, 0, 0, DPR, 0, 0);
  const sky = g.createLinearGradient(0, 0, 0, H);
  sky.addColorStop(0, "#050716");
  sky.addColorStop(0.6, "#0c1137");
  sky.addColorStop(1, "#190c35");
  g.fillStyle = sky;
  g.fillRect(0, 0, W, H);
  const glow = g.createRadialGradient(W / 2, 0, 10, W / 2, 0, H * 0.75);
  glow.addColorStop(0, "rgba(255,46,77,.18)");
  glow.addColorStop(1, "rgba(255,46,77,0)");
  g.fillStyle = glow;
  g.fillRect(0, 0, W, H);
  g.fillStyle = "#cfe9ff";
  for (let i = 0; i < 60; i++) {
    g.globalAlpha = rand(0.2, 0.85);
    g.beginPath();
    g.arc(rand(0, W), rand(0, LINE_Y), rand(0.5, 1.6) * S, 0, TAU);
    g.fill();
  }
  g.globalAlpha = 1;
  const base = g.createLinearGradient(0, LINE_Y, 0, H);
  base.addColorStop(0, "#0a0d25");
  base.addColorStop(1, "#03040d");
  g.fillStyle = base;
  g.fillRect(0, LINE_Y, W, H - LINE_Y);
}

/* ---------- targets ---------- */
function pickDrift(t) {
  let sp = rand(t.drift[0], t.drift[1]) * Ws;
  if (t.final && Math.random() < 0.3) sp *= 1.35;           // sudden dash
  t.vxT = (Math.random() < 0.5 ? -1 : 1) * sp;
  t.chg = rand(t.span[0], t.span[1]);
}

function makeTargets() {
  const n = CONFIG.TARGET_COUNT, lo = CONFIG.NORMAL_SPEED[0], hi = CONFIG.NORMAL_SPEED[1];
  const cols = shuffle(Array.from({ length: n }, (_, i) => (i + 0.5) / n));
  const rows = shuffle(Array.from({ length: n }, (_, i) => 0.06 + i * 0.07));
  const spd = shuffle(Array.from({ length: n }, (_, i) => lo + (hi - lo) * (n > 1 ? i / (n - 1) : 0) + rand(-1, 1)));
  targets.length = 0;
  for (let i = 0; i < n; i++) {
    const t = {
      x: clamp((cols[i] + rand(-0.04, 0.04)) * W, 46 * S, W - 46 * S),
      y: rows[i] * H + 8 * S,
      w: 74 * S, h: 84 * S, sc: 1, scT: 1, hb: CONFIG.HITBOX,
      vy: spd[i] * Hs, vx: 0, vxT: 0, chg: 0,
      drift: [26, 68], span: [0.9, 2.2], ease: 2.6,
      phase: rand(0, TAU), state: "alive", hitT: 0, final: false
    };
    pickDrift(t);
    t.vx = t.vxT * 0.6;
    targets.push(t);
  }
}

function enrage(t) {          // the last target: much faster and much harder to predict
  t.final = true;
  const remaining = LINE_Y - (t.y + t.h / 2);
  let vy = CONFIG.FINAL_SPEED * Hs;
  if (remaining / vy < CONFIG.FINAL_MIN_TIME) vy = Math.max(t.vy * 1.8, remaining / CONFIG.FINAL_MIN_TIME);   // never an unavoidable instant loss
  t.vy = vy;
  t.scT = CONFIG.FINAL_SCALE;
  t.hb = CONFIG.FINAL_HITBOX;
  t.drift = CONFIG.FINAL_DRIFT; t.span = CONFIG.FINAL_SPAN; t.ease = CONFIG.FINAL_EASE;
  pickDrift(t);
  t.vx = t.vxT;
  flash = Math.max(flash, 0.55);
  shake = Math.max(shake, 0.5);
  sfx("rage"); buzz([40, 30, 60]);
}

function updateTargets(dt) {
  for (const t of targets) {
    if (t.state === "hit") {
      t.hitT += dt;
      if (t.hitT >= HIT_TIME) t.state = "gone";
      continue;
    }
    if (t.state !== "alive" || state !== "playing") continue;
    t.sc += (t.scT - t.sc) * Math.min(1, 12 * dt);
    t.w = 74 * S * t.sc; t.h = 84 * S * t.sc;
    t.chg -= dt;
    if (t.chg <= 0) pickDrift(t);
    t.vx += (t.vxT - t.vx) * Math.min(1, t.ease * dt);
    t.x += t.vx * dt;
    t.y += t.vy * (t.final ? 1 + 0.16 * Math.sin(time * 5 + t.phase) : 1) * dt;
    const half = t.w / 2 + 2 * S;
    if (t.x < half) { t.x = half; t.vx = Math.abs(t.vx); t.vxT = Math.abs(t.vxT); }
    else if (t.x > W - half) { t.x = W - half; t.vx = -Math.abs(t.vx); t.vxT = -Math.abs(t.vxT); }
  }
}

/* ---------- cannon + projectiles ---------- */
function aimAt(x, y) {
  const dx = x - cannon.x, dy = Math.max(cannon.y - y, 150 * S);
  return clamp(Math.atan2(dx, dy), -1.05, 1.05);
}

function updateCannon(dt) {
  if (pointer.has) cannon.x += (clamp(pointer.x, 28 * S, W - 28 * S) - cannon.x) * Math.min(1, 16 * dt);
  const aiming = pointer.has && (pointer.down || pointer.mouse);
  cannon.angle += ((aiming ? aimAt(pointer.x, pointer.y) : 0) - cannon.angle) * Math.min(1, 20 * dt);
}

function fire() {
  const a = cannon.angle, len = 54 * S, sp = CONFIG.BULLET_SPEED * Hs;
  bullets.push({
    x: cannon.x + Math.sin(a) * len,
    y: cannon.y - 12 * S - Math.cos(a) * len,
    vx: Math.sin(a) * sp,
    vy: -Math.cos(a) * sp,
    r: 5.5 * S,
    dead: false
  });
  cannon.recoil = 1;
  sfx("shoot");
}

function collide() {
  for (const b of bullets) {
    for (const t of targets) {
      if (b.dead) break;
      if (t.state !== "alive") continue;
      if (Math.abs(b.x - t.x) < t.w * t.hb + b.r && Math.abs(b.y - t.y) < t.h * t.hb + b.r) {
        b.dead = true;
        hit(t);
      }
    }
  }
  for (let i = bullets.length - 1; i >= 0; i--) if (bullets[i].dead) bullets.splice(i, 1);
}

/* ---------- game flow ---------- */
function hit(t) {
  t.state = "hit"; t.hitT = 0; t.vx = 0;
  explode(t.x, t.y, Math.max(t.w, t.h));
  showToast("A SHORT PERSON HAS BEEN SHOT DOWN.");
  shake = Math.max(shake, 0.35);
  sfx("hit"); buzz(30);
}

function checkFlow() {
  const alive = targets.filter(t => t.state === "alive");
  if (alive.length === 0) {                               // all four are down
    state = "winning"; endTimer = 1.5; bullets.length = 0;
    sfx("win");
  } else if (alive.length === 1 && !alive[0].final) {     // only one photo left
    enrage(alive[0]);
  }
}

function checkBreach() {
  for (const t of targets) {
    if (t.state === "alive" && t.y + t.h / 2 >= LINE_Y) {
      breached = true; flash = 1; shake = 1;
      sfx("breach"); buzz([90, 40, 160]);
      finish("lose");
      return;
    }
  }
}

function finish(result) {
  state = "over"; overAt = time;
  toastEl.classList.remove("show");
  const win = result === "win";
  endTitle.textContent = win ? "DEFENCE SUCCESSFULLY PROTECTED." : "DEFENCE BREACHED";
  endSub.textContent = win ? "That was unnecessarily difficult." : "YOU ARE TOO SHORT TO CAUSE ANY HARM.";
  endEl.className = "screen end " + (win ? "win" : "lose");
  void endEl.offsetWidth;                                 // restart the reveal animation
  endEl.classList.add("show");
  setTimeout(() => {                                        // REPLAY becomes tappable only now
    if (state !== "over") return;                            // a new round already started - leave it disabled
    endEl.classList.add("ready");
    replayBtn.disabled = false;
  }, 2300);
}

function startRound() {                                   // used by PLAY and by REPLAY
  if (state === "playing" || state === "winning") return;
  targets.length = 0; bullets.length = 0; fx.length = 0;
  breached = false; shake = 0; flash = 0; fireT = CONFIG.FIRE_INTERVAL * 0.4; tapT = -1;
  cannon.angle = 0; cannon.recoil = 0; cannon.x = W / 2;
  pointer.has = false; pointer.down = false;
  toastEl.classList.remove("show");
  introEl.classList.add("hidden");
  endEl.className = "screen end hidden";
  replayBtn.disabled = true;
  makeTargets();
  state = "playing";
  startLoop();
  sfx("start");
}

function startLoop() {
  if (raf) return;
  last = performance.now();
  raf = requestAnimationFrame(frame);
}

/* ---------- cartoon explosion ---------- */
function explode(x, y, size) {
  const R = size * 0.95;
  fx.push({ k: "burst", x, y, R, t: 0, life: 0.62, rot: rand(-0.3, 0.3), jit: Array.from({ length: 12 }, () => rand(0.82, 1.15)) });
  fx.push({ k: "ring", x, y, R, t: 0, life: 0.5 });
  for (let i = 0; i < 8; i++) {
    const a = (i / 8) * TAU + rand(-0.3, 0.3), v = rand(70, 150) * S;
    fx.push({ k: "puff", x, y, vx: Math.cos(a) * v, vy: Math.sin(a) * v, r: rand(11, 19) * S, t: 0, life: rand(0.5, 0.75) });
  }
  const cols = ["#ffe14d", "#ff3d81", "#19f0ff", "#39ff88", "#ff9f1c", "#ffffff"];
  for (let i = 0; i < 22; i++) {
    const a = rand(0, TAU), v = rand(140, 380) * S;
    fx.push({ k: "conf", x, y, vx: Math.cos(a) * v, vy: Math.sin(a) * v - 90 * S, rot: rand(0, TAU), vr: rand(-12, 12), s: rand(5, 10) * S, c: pick(cols), t: 0, life: rand(0.7, 1.1) });
  }
  fx.push({ k: "word", x, y: y - R * 0.15, text: pick(["POW!", "BAM!", "ZAP!", "BOOM!", "WHAM!", "POOF!"]), rot: rand(-0.25, 0.25), size: 32 * S, t: 0, life: 0.9 });
}

function updateFx(dt) {
  const drag = Math.pow(0.03, dt);
  for (let i = fx.length - 1; i >= 0; i--) {
    const f = fx[i];
    f.t += dt;
    if (f.t >= f.life) { fx.splice(i, 1); continue; }
    if (f.vx === undefined) continue;
    f.x += f.vx * dt;
    f.y += f.vy * dt;
    if (f.k === "conf") { f.vy += 760 * S * dt; f.vx *= Math.pow(0.2, dt); f.rot += f.vr * dt; }
    else { f.vx *= drag; f.vy *= drag; }
  }
}

function drawFx(f) {
  const p = f.t / f.life;
  ctx.save();
  switch (f.k) {
    case "burst": {                                        // comic starburst
      const r = f.R * (0.2 + 0.9 * easeOutBack(Math.min(1, p / 0.4)));
      ctx.globalAlpha = p < 0.5 ? 1 : 1 - (p - 0.5) / 0.5;
      ctx.translate(f.x, f.y);
      ctx.rotate(f.rot + p * 0.6);
      ctx.lineJoin = "round";
      starPath(r, r * 0.55, f.jit);
      ctx.fillStyle = "#ffdd33"; ctx.strokeStyle = "#ff6a00"; ctx.lineWidth = 4 * S;
      ctx.fill(); ctx.stroke();
      starPath(r * 0.6, r * 0.34, f.jit);
      ctx.fillStyle = "#fff7b8"; ctx.fill();
      break;
    }
    case "ring":
      ctx.globalAlpha = 1 - p;
      ctx.strokeStyle = "#ffffff";
      ctx.lineWidth = (7 - 5 * p) * S;
      ctx.beginPath(); ctx.arc(f.x, f.y, f.R * (0.3 + 1.4 * p), 0, TAU); ctx.stroke();
      break;
    case "puff":                                           // cartoon smoke cloud
      ctx.globalAlpha = 1 - p;
      ctx.beginPath(); ctx.arc(f.x, f.y, f.r * (0.6 + 1.1 * Math.min(1, p * 2)), 0, TAU);
      ctx.fillStyle = "#fbfdff"; ctx.strokeStyle = "#8fb4ff"; ctx.lineWidth = 2.5 * S;
      ctx.fill(); ctx.stroke();
      break;
    case "conf":                                           // confetti
      ctx.globalAlpha = p < 0.7 ? 1 : 1 - (p - 0.7) / 0.3;
      ctx.translate(f.x, f.y); ctx.rotate(f.rot);
      ctx.fillStyle = f.c;
      ctx.fillRect(-f.s / 2, -f.s / 4, f.s, f.s / 2);
      break;
    case "word": {                                         // POW! / BAM! ...
      const sc = easeOutBack(Math.min(1, p / 0.25));
      ctx.globalAlpha = p < 0.7 ? 1 : 1 - (p - 0.7) / 0.3;
      ctx.translate(f.x, f.y - p * 26 * S);
      ctx.rotate(f.rot); ctx.scale(sc, sc);
      ctx.font = "italic 900 " + Math.round(f.size) + "px " + FONT;
      ctx.textAlign = "center"; ctx.textBaseline = "middle"; ctx.lineJoin = "round";
      ctx.lineWidth = 8 * S; ctx.strokeStyle = "#0a1020"; ctx.strokeText(f.text, 0, 0);
      ctx.fillStyle = "#fff36b"; ctx.fillText(f.text, 0, 0);
      break;
    }
  }
  ctx.restore();
}

/* ---------- drawing helpers ---------- */
function rr(x, y, w, h, r) {                               // rounded rectangle path
  r = Math.min(r, w / 2, h / 2);
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.arcTo(x + w, y, x + w, y + h, r);
  ctx.arcTo(x + w, y + h, x, y + h, r);
  ctx.arcTo(x, y + h, x, y, r);
  ctx.arcTo(x, y, x + w, y, r);
  ctx.closePath();
}

function starPath(ro, ri, jit) {                           // spiky starburst path around (0,0)
  const n = jit.length;
  ctx.beginPath();
  for (let i = 0; i < n * 2; i++) {
    const r = i % 2 ? ri : ro * jit[i >> 1], a = (i / (n * 2)) * TAU;
    const px = Math.cos(a) * r, py = Math.sin(a) * r;
    if (i) ctx.lineTo(px, py); else ctx.moveTo(px, py);
  }
  ctx.closePath();
}

function drawCover(img, x, y, w, h) {                      // "object-fit: cover" for the photo
  const ir = img.naturalWidth / img.naturalHeight, r = w / h;
  let sw = img.naturalWidth, sh = img.naturalHeight, sx = 0, sy = 0;
  if (ir > r) { sw = sh * r; sx = (img.naturalWidth - sw) / 2; }
  else { sh = sw / r; sy = (img.naturalHeight - sh) * 0.3; }
  ctx.drawImage(img, sx, sy, sw, sh, x, y, w, h);
}

function placeholder(x, y, w, h) {                         // shown only if the photo fails to load
  const g = ctx.createLinearGradient(0, y, 0, y + h);
  g.addColorStop(0, "#3a4a8a"); g.addColorStop(1, "#1a2050");
  ctx.fillStyle = g; ctx.fillRect(x, y, w, h);
  ctx.fillStyle = "#aebcff";
  ctx.beginPath(); ctx.arc(0, y + h * 0.38, w * 0.2, 0, TAU); ctx.fill();
  ctx.beginPath(); ctx.ellipse(0, y + h * 0.98, w * 0.38, h * 0.32, 0, 0, TAU); ctx.fill();
}

function drawGrid() {
  const gap = 42 * S, off = (time * 18 * S) % gap;
  ctx.strokeStyle = "rgba(25,240,255,.07)";
  ctx.lineWidth = 1;
  ctx.beginPath();
  for (let y = off - gap; y < LINE_Y; y += gap) { ctx.moveTo(0, y); ctx.lineTo(W, y); }
  for (let x = 0; x <= W; x += gap) { ctx.moveTo(x, 0); ctx.lineTo(x, LINE_Y); }
  ctx.stroke();
}

function drawLine() {
  const y = LINE_Y;
  const col = breached ? (((time * 10) | 0) % 2 ? "255,46,77" : "255,255,255") : "25,240,255";
  const bh = 9 * S, sw = 15 * S, off = (time * 28 * S) % (sw * 2);
  ctx.save();                                              // hazard tape under the line
  ctx.beginPath(); ctx.rect(0, y, W, bh); ctx.clip();
  ctx.fillStyle = "#ffd21f"; ctx.fillRect(0, y, W, bh);
  ctx.fillStyle = "#15151c";
  for (let x = -sw * 2 + off; x < W + sw; x += sw * 2) {
    ctx.beginPath();
    ctx.moveTo(x, y + bh); ctx.lineTo(x + sw, y + bh); ctx.lineTo(x + sw + bh, y); ctx.lineTo(x + bh, y);
    ctx.closePath(); ctx.fill();
  }
  ctx.restore();
  const pulse = 0.75 + 0.25 * Math.sin(time * 5);          // neon line
  ctx.lineCap = "butt";
  const layers = [[12, 0.08 * pulse], [7, 0.16 * pulse], [3, 1]];
  for (const l of layers) {
    ctx.strokeStyle = "rgba(" + col + "," + l[1] + ")";
    ctx.lineWidth = l[0] * S;
    ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(W, y); ctx.stroke();
  }
  ctx.fillStyle = "rgba(" + col + ",.9)";
  ctx.font = "800 " + Math.round(11 * S) + "px " + FONT;
  ctx.textAlign = "left"; ctx.textBaseline = "bottom";
  ctx.fillText("DEFENCE LINE", 10 * S, y - 7 * S);
}

function drawTarget(t) {
  const w = t.w, h = t.h, x = -w / 2, y = -h / 2;
  const hitP = t.state === "hit" ? t.hitT / HIT_TIME : 0;
  const live = t.state === "alive";
  const rgb = t.final ? "255,46,77" : "255,176,32";
  ctx.save();
  ctx.translate(t.x + (t.final && live ? rand(-1.6, 1.6) * S : 0), t.y + (t.final && live ? rand(-1.2, 1.2) * S : 0));
  ctx.rotate(Math.sin(time * 2.4 + t.phase) * 0.05);
  const pop = 1 + 0.24 * Math.sin(Math.min(1, hitP * 1.5) * Math.PI);
  ctx.scale(pop, pop);

  if (t.final && live) {                                   // speed streaks trailing above the last target
    ctx.strokeStyle = "rgba(255,90,90,.75)";
    ctx.lineWidth = 3 * S;
    ctx.lineCap = "round";
    for (let i = -1.5; i <= 1.5; i++) {
      const lx = i * w * 0.26, ll = (16 + Math.abs((time * 37 + i * 13) % 22)) * S;
      ctx.beginPath(); ctx.moveTo(lx, y - 10 * S); ctx.lineTo(lx, y - 10 * S - ll); ctx.stroke();
    }
  }

  const fx0 = x - 3 * S, fy0 = y - 3 * S, fw = w + 6 * S, fh = h + 6 * S, fr = 17 * S;
  const glows = [[16, 0.08], [10, 0.14], [5, 0.32]];
  for (const gl of glows) {                                // neon glow
    rr(fx0, fy0, fw, fh, fr);
    ctx.strokeStyle = "rgba(" + rgb + "," + gl[1] + ")";
    ctx.lineWidth = gl[0] * S;
    ctx.stroke();
  }
  rr(fx0, fy0, fw, fh, fr);                                // white sticker frame
  ctx.fillStyle = "#fff"; ctx.fill();
  ctx.lineWidth = 2.5 * S; ctx.strokeStyle = "#0a1020"; ctx.stroke();

  ctx.save();                                              // the photo
  rr(x, y, w, h, 14 * S);
  ctx.clip();
  if (photoReady) drawCover(photo, x, y, w, h); else placeholder(x, y, w, h);
  if (hitP > 0) {
    ctx.fillStyle = "rgba(255,255,255," + (0.3 + 0.6 * Math.pow(Math.sin(hitP * Math.PI * 3), 2)) + ")";
    ctx.fillRect(x, y, w, h);
  }
  ctx.restore();

  const pad = (9 + Math.sin(time * (t.final ? 11 : 6) + t.phase) * 2) * S, len = 11 * S;   // lock-on corners
  ctx.strokeStyle = "rgb(" + rgb + ")";
  ctx.lineWidth = 3 * S; ctx.lineCap = "round"; ctx.lineJoin = "round";
  for (const c of [[-1, -1], [1, -1], [1, 1], [-1, 1]]) {
    const cx = c[0] * (w / 2 + pad), cy = c[1] * (h / 2 + pad);
    ctx.beginPath(); ctx.moveTo(cx - c[0] * len, cy); ctx.lineTo(cx, cy); ctx.lineTo(cx, cy - c[1] * len); ctx.stroke();
  }
  ctx.restore();
}

function drawBullet(b) {
  const sp = Math.hypot(b.vx, b.vy) || 1, tx = b.vx / sp, ty = b.vy / sp, len = 20 * S;
  ctx.lineCap = "round";
  ctx.strokeStyle = "rgba(255,190,60,.35)";
  ctx.lineWidth = b.r * 1.8;
  ctx.beginPath(); ctx.moveTo(b.x - tx * len, b.y - ty * len); ctx.lineTo(b.x, b.y); ctx.stroke();
  const g = ctx.createRadialGradient(b.x - b.r * 0.3, b.y - b.r * 0.3, 1, b.x, b.y, b.r);
  g.addColorStop(0, "#ffffff"); g.addColorStop(0.45, "#ffe14d"); g.addColorStop(1, "#ff8a00");
  ctx.beginPath(); ctx.arc(b.x, b.y, b.r, 0, TAU);
  ctx.fillStyle = g; ctx.fill();
  ctx.lineWidth = 2 * S; ctx.strokeStyle = "#0a1020"; ctx.stroke();
}

function drawCannon() {
  const s = S;
  ctx.save();
  ctx.translate(cannon.x, cannon.y);
  ctx.lineJoin = "round";
  ctx.strokeStyle = "#0a1020";
  ctx.lineWidth = 3 * s;

  ctx.fillStyle = "rgba(0,0,0,.4)";                        // ground shadow
  ctx.beginPath(); ctx.ellipse(0, 26 * s, 40 * s, 7 * s, 0, 0, TAU); ctx.fill();

  for (const sx of [-24, 24]) {                            // wheels
    ctx.beginPath(); ctx.arc(sx * s, 13 * s, 14 * s, 0, TAU);
    ctx.fillStyle = "#2a3150"; ctx.fill(); ctx.stroke();
    ctx.beginPath(); ctx.arc(sx * s, 13 * s, 5.5 * s, 0, TAU);
    ctx.fillStyle = "#ffb020"; ctx.fill(); ctx.stroke();
  }

  ctx.save();                                              // barrel: turns on its pivot, kicks back when firing
  ctx.translate(0, -12 * s);
  ctx.rotate(cannon.angle);
  const kick = cannon.recoil * 9 * s;
  const g = ctx.createLinearGradient(-11 * s, 0, 11 * s, 0);
  g.addColorStop(0, "#0d8ea8"); g.addColorStop(0.4, "#46f3ff"); g.addColorStop(1, "#0a7690");
  rr(-11 * s, -44 * s + kick, 22 * s, 58 * s, 8 * s);
  ctx.fillStyle = g; ctx.fill(); ctx.stroke();
  rr(-14.5 * s, -50 * s + kick, 29 * s, 13 * s, 5 * s);    // muzzle ring
  ctx.fillStyle = "#ffb020"; ctx.fill(); ctx.stroke();
  if (cannon.recoil > 0.55) {                              // muzzle flash
    ctx.save();
    ctx.translate(0, -58 * s + kick);
    starPath(15 * s * cannon.recoil, 6 * s, JIT6);
    ctx.fillStyle = "#fff6b0"; ctx.strokeStyle = "#ff9f1c"; ctx.lineWidth = 2 * s;
    ctx.fill(); ctx.stroke();
    ctx.restore();
  }
  ctx.restore();

  const c = ctx.createLinearGradient(0, -8 * s, 0, 20 * s); // carriage
  c.addColorStop(0, "#ffcf4d"); c.addColorStop(1, "#f28a00");
  rr(-31 * s, -8 * s, 62 * s, 26 * s, 10 * s);
  ctx.fillStyle = c; ctx.fill(); ctx.stroke();
  ctx.beginPath(); ctx.arc(0, -12 * s, 8 * s, 0, TAU);     // pivot cap
  ctx.fillStyle = "#2a3150"; ctx.fill(); ctx.stroke();
  ctx.strokeStyle = "rgba(255,255,255,.55)"; ctx.lineWidth = 2.5 * s; ctx.lineCap = "round";
  ctx.beginPath(); ctx.moveTo(-22 * s, -1 * s); ctx.lineTo(-10 * s, -1 * s); ctx.stroke();
  ctx.restore();
}

function render() {
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.clearRect(0, 0, W, H);
  ctx.save();
  if (shake > 0) {
    const amp = shake * (CALM ? 3 : 9) * S;
    ctx.translate(rand(-1, 1) * amp, rand(-1, 1) * amp);
  }
  ctx.drawImage(bg, 0, 0, W, H);
  drawGrid();
  drawLine();
  for (const t of targets) if (t.state !== "gone") drawTarget(t);
  for (const b of bullets) drawBullet(b);
  drawCannon();
  for (const f of fx) drawFx(f);
  ctx.restore();
  if (flash > 0) {
    ctx.fillStyle = "rgba(255,40,70," + Math.min(0.4, flash * 0.4) * (CALM ? 0.4 : 1) + ")";
    ctx.fillRect(0, 0, W, H);
  }
}

/* ---------- message, sound, vibration ---------- */
function showToast(msg) {
  toastEl.textContent = msg;
  toastEl.classList.remove("show");
  void toastEl.offsetWidth;                                // restart the animation
  toastEl.classList.add("show");
}

let actx = null;
function initAudio() {
  if (!CONFIG.SOUND) return;
  try {
    if (!actx) actx = new (window.AudioContext || window.webkitAudioContext)();
    if (actx.state === "suspended") actx.resume();
  } catch (_) { actx = null; }
}

function tone(type, f0, f1, dur, vol) {
  if (!actx) return;
  const t = actx.currentTime, o = actx.createOscillator(), g = actx.createGain();
  o.type = type;
  o.frequency.setValueAtTime(f0, t);
  o.frequency.exponentialRampToValueAtTime(Math.max(30, f1), t + dur);
  g.gain.setValueAtTime(vol, t);
  g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
  o.connect(g).connect(actx.destination);
  o.start(t); o.stop(t + dur + 0.02);
}

function sfx(name) {
  switch (name) {
    case "start": tone("square", 330, 660, 0.15, 0.04); break;
    case "shoot": tone("square", 680, 260, 0.08, 0.025); break;
    case "hit": tone("sawtooth", 320, 50, 0.32, 0.07); tone("square", 900, 200, 0.18, 0.03); break;
    case "rage": tone("sawtooth", 180, 620, 0.35, 0.05); break;
    case "breach": tone("sawtooth", 420, 40, 0.9, 0.08); break;
    case "win": [523, 659, 784, 1047].forEach((f, i) => setTimeout(() => tone("triangle", f, f, 0.18, 0.06), i * 110)); break;
  }
}

function buzz(pattern) {
  try { if (navigator.vibrate) navigator.vibrate(pattern); } catch (_) {}
}

/* ---------- main loop ---------- */
function update(dt) {
  shake = Math.max(0, shake - dt * 2.4);
  flash = Math.max(0, flash - dt * 2.2);
  cannon.recoil = Math.max(0, cannon.recoil - dt * 6);
  updateFx(dt);
  if (state === "intro") return;
  updateTargets(dt);                                       // shot targets finish vanishing in every state
  if (state === "playing") {
    updateCannon(dt);
    if (pointer.down) {                                       // fires only while the screen is held - no auto-fire
      fireT += dt;
      if (fireT >= CONFIG.FIRE_INTERVAL) { fireT = 0; fire(); }
    }
    for (const b of bullets) {
      b.x += b.vx * dt; b.y += b.vy * dt;
      if (b.y < -30 || b.x < -30 || b.x > W + 30) b.dead = true;
    }
    collide();
    checkFlow();
    if (state === "playing") checkBreach();
  } else if (state === "winning") {
    endTimer -= dt;
    if (endTimer <= 0) finish("win");
  }
}

function frame(now) {
  raf = requestAnimationFrame(frame);
  const dt = clamp((now - last) / 1000, 0, 0.033);
  last = now;
  time += dt;
  update(dt);
  render();
  if (state === "over" && time - overAt > 1.8) { cancelAnimationFrame(raf); raf = 0; }   // idle while the ending is on screen
}

/* ---------- input: tap to aim + fire, drag to move ---------- */
function setPointer(e) {
  const r = canvas.getBoundingClientRect();
  pointer.x = e.clientX - r.left;
  pointer.y = e.clientY - r.top;
  pointer.has = true;
  pointer.mouse = e.pointerType === "mouse";
}

canvas.addEventListener("pointerdown", e => {
  e.preventDefault();
  try { canvas.setPointerCapture(e.pointerId); } catch (_) {}
  pointer.down = true;
  setPointer(e);
  if (state === "playing" && time - tapT > CONFIG.TAP_COOLDOWN) {   // a tap aims at that spot and fires right away
    tapT = time;
    cannon.angle = aimAt(pointer.x, pointer.y);
    fire();
    fireT = 0;
  }
});
canvas.addEventListener("pointermove", e => {
  if (pointer.down || e.pointerType === "mouse") { e.preventDefault(); setPointer(e); }
});
const release = () => { pointer.down = false; };
canvas.addEventListener("pointerup", release);
canvas.addEventListener("pointercancel", release);

/* ---------- password screen ---------- */
function tryUnlock() {
  const attempt = pwInput.value.trim().toLowerCase();
  if (attempt && sha256(attempt) === CONFIG.PASSWORD_HASH) {
    pwError.textContent = "";
    pwInput.value = "";
    lockEl.classList.add("hidden");
    introEl.classList.remove("hidden");                    // the opening screen appears only now
    startLoop();
  } else {
    pwError.textContent = attempt ? "Wrong password. Try again." : "Type the password first.";
    pwInput.value = "";
    lockEl.classList.remove("shake");
    void lockEl.offsetWidth;
    lockEl.classList.add("shake");
    pwInput.focus();
    buzz(60);
  }
}
unlockBtn.addEventListener("click", tryUnlock);
pwInput.addEventListener("keydown", e => { if (e.key === "Enter") tryUnlock(); });
pwInput.addEventListener("input", () => { pwError.textContent = ""; });
pwToggle.addEventListener("click", () => {
  const show = pwInput.type === "password";
  pwInput.type = show ? "text" : "password";
  pwToggle.textContent = show ? "Hide" : "Show";
  pwToggle.setAttribute("aria-label", show ? "Hide password" : "Show password");
});

/* ---------- boot ---------- */
layout();
window.addEventListener("resize", layout);
window.addEventListener("orientationchange", () => setTimeout(layout, 250));
if (window.ResizeObserver) new ResizeObserver(() => layout()).observe(gameEl);

playBtn.addEventListener("click", () => { initAudio(); startRound(); });
replayBtn.addEventListener("click", () => { if (state === "over") { initAudio(); startRound(); } });

document.addEventListener("touchmove", e => { if (e.target.tagName !== "INPUT") e.preventDefault(); }, { passive: false });
document.addEventListener("contextmenu", e => e.preventDefault());
document.addEventListener("gesturestart", e => e.preventDefault());
