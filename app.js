/* Inside my mind — a zoomable, searchable hand-drawn mind map.
 *
 * data/strokes.js  every pen stroke of the map (built by tools/build_strokes.py)
 * data/index.js    the transcribed handwriting + topic regions that power search
 *
 * No dependencies, no build step. */
(function () {
'use strict';

const $ = (sel, el) => (el || document).querySelector(sel);
const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
const META = window.MIND_META;
const INDEX = window.MIND_INDEX || { regions: [], items: [] };
const reduceMotion = matchMedia('(prefers-reduced-motion: reduce)').matches;

const stage = $('#stage'), cv = $('#ink'), fx = $('#fx'), labelsEl = $('#labels');
const panel = $('#panel'), mini = $('#mini'), minimapEl = $('#minimap');
const ctx = cv.getContext('2d', { alpha: false });
const fctx = fx.getContext('2d');
const snap = document.createElement('canvas');           // last sharp frame, reused while moving
const sctx = snap.getContext('2d', { alpha: false });
const ov = document.createElement('canvas');             // whole map at low resolution
const octx = ov.getContext('2d');

if (!META || !window.MIND_STROKES) { $('#loader').textContent = 'Could not load the map data.'; return; }

/* ================================================================ data */
const N = META.count;
const off = new Uint32Array(N + 1);       // stroke -> first point
const col = new Uint8Array(N);            // stroke -> palette index
const wid = new Float32Array(N);          // stroke -> pen width (map units)
const bb = new Float32Array(N * 4);       // stroke -> bounding box
const pts = new Float32Array(META.points * 2);
let batches = [];

function decode() {
  const bin = atob(window.MIND_STROKES);
  window.MIND_STROKES = null;
  const len = bin.length, bytes = new Uint8Array(len);
  for (let i = 0; i < len; i++) bytes[i] = bin.charCodeAt(i);
  const Q = META.q;
  let i = 0, p = 0;
  const rv = () => { let v = 0, s = 0, b; do { b = bytes[i++]; v |= (b & 127) << s; s += 7; } while (b & 128); return v; };
  for (let s = 0; s < N; s++) {
    col[s] = bytes[i++];
    wid[s] = rv() / 100;
    const n = rv();
    off[s] = p;
    let x = 0, y = 0, x0 = 1e9, y0 = 1e9, x1 = -1e9, y1 = -1e9;
    for (let j = 0; j < n; j++) {
      let v = rv(); x += (v >>> 1) ^ -(v & 1);
      v = rv(); y += (v >>> 1) ^ -(v & 1);
      const fx_ = x / Q, fy_ = y / Q;
      pts[2 * p] = fx_; pts[2 * p + 1] = fy_; p++;
      if (fx_ < x0) x0 = fx_; if (fx_ > x1) x1 = fx_;
      if (fy_ < y0) y0 = fy_; if (fy_ > y1) y1 = fy_;
    }
    bb[4 * s] = x0; bb[4 * s + 1] = y0; bb[4 * s + 2] = x1; bb[4 * s + 3] = y1;
  }
  off[N] = p;
}

/* Strokes are grouped by pen style so each style is one canvas path. "White" ink is the
 * eraser / knocked-out text, so the order of white vs. coloured runs is kept intact. */
const WHITE = META.colors.indexOf('#ffffff');
function buildBatches() {
  let map = new Map(), lastWhite = null;
  const out = [];
  for (let s = 0; s < N; s++) {
    const isWhite = col[s] === WHITE;
    if (isWhite !== lastWhite) { map = new Map(); lastWhite = isWhite; }
    const w = wid[s];
    const wq = w < 2 ? Math.round(w * 10) / 10 : w < 5 ? Math.round(w * 4) / 4 : Math.round(w * 2) / 2;
    const dot = off[s + 1] - off[s] === 1;
    const key = col[s] + '|' + wq + '|' + dot;
    let b = map.get(key);
    if (!b) { b = { c: col[s], w: Math.max(wq, 0.1), dot, ids: [] }; map.set(key, b); out.push(b); }
    b.ids.push(s);
  }
  for (const b of out) b.ids = Int32Array.from(b.ids);
  batches = out;
}

/* The canvas has a few stray specks near its corners; frame the part that matters. */
let bounds = { x0: 0, y0: 0, x1: META.w, y1: META.h };
function computeBounds() {
  const xs = new Float32Array(N), ys = new Float32Array(N);
  for (let s = 0; s < N; s++) { xs[s] = (bb[4 * s] + bb[4 * s + 2]) / 2; ys[s] = (bb[4 * s + 1] + bb[4 * s + 3]) / 2; }
  xs.sort(); ys.sort();
  const lo = Math.floor(N * 0.002), hi = Math.min(N - 1, Math.ceil(N * 0.998));
  const pad = 110;
  bounds = { x0: xs[lo] - pad, y0: ys[lo] - pad, x1: xs[hi] + pad, y1: ys[hi] + pad };
}

/* =============================================================== theme */
let palette = [], paper = '#fff', dotRGB = '0,0,0', dotA = 0.15, marker = '#f6c443';

function hexToHsl(hex) {
  const r = parseInt(hex.slice(1, 3), 16) / 255, g = parseInt(hex.slice(3, 5), 16) / 255, b = parseInt(hex.slice(5, 7), 16) / 255;
  const mx = Math.max(r, g, b), mn = Math.min(r, g, b), l = (mx + mn) / 2;
  let h = 0, s = 0;
  if (mx !== mn) {
    const d = mx - mn;
    s = l > 0.5 ? d / (2 - mx - mn) : d / (mx + mn);
    h = mx === r ? (g - b) / d + (g < b ? 6 : 0) : mx === g ? (b - r) / d + 2 : (r - g) / d + 4;
    h *= 60;
  }
  return [h, s, l];
}
function readTheme() {
  const cs = getComputedStyle(document.documentElement);
  const dark = document.documentElement.dataset.theme === 'dark';
  paper = cs.getPropertyValue('--paper').trim() || '#fff';
  marker = cs.getPropertyValue('--marker').trim() || '#f6c443';
  const m = /rgba?\(([^)]+)\)/.exec(cs.getPropertyValue('--dot'));
  if (m) { const v = m[1].split(',').map(parseFloat); dotRGB = v.slice(0, 3).join(','); dotA = v[3] == null ? 1 : v[3]; }
  // the pen colours of the drawing, nudged so they read well on this theme's paper
  palette = META.colors.map(hex => {
    let [h, s, l] = hexToHsl(hex);
    if (l > 0.97) return paper;
    if (dark) l = s < 0.2 ? 0.86 : Math.max(l, 0.64);
    else l = s < 0.2 ? Math.min(l, 0.29) : Math.min(l, 0.53);
    return 'hsl(' + h.toFixed(0) + ' ' + (s * 100).toFixed(0) + '% ' + (l * 100).toFixed(0) + '%)';
  });
  const tc = $('meta[name="theme-color"]'); if (tc) tc.content = paper;
}

/* ================================================================ view */
let W = 1, H = 1, dpr = 1;
const view = { x: 0, y: 0, k: 1 };        // map point at the viewport centre + CSS px per map unit
let kFit = 0.3, kMin = 0.1;
const K_MAX = 12, K_READ = 4.2;           // deepest zoom / zoom at which the small handwriting reads comfortably
let kOv = 0.5;                            // device px per map unit of the overview bitmap
let insets = { l: 0, t: 0, r: 0, b: 0 };  // part of the viewport hidden under the panel

function measure() {
  W = stage.clientWidth; H = stage.clientHeight;
  dpr = Math.min(window.devicePixelRatio || 1, 2);
  for (const c of [cv, fx, snap]) { c.width = Math.round(W * dpr); c.height = Math.round(H * dpr); }
  updateInsets();
  const f = fitView(bounds, 0);
  kFit = f.k; kMin = kFit * 0.6;
  snapView = null;
}
/* the panel floats over the map: beside it on wide screens, above it on phones */
function updateInsets() {
  const r = panel.getBoundingClientRect();
  insets = W > 760 ? { l: r.right + 6, t: 0, r: 0, b: 0 } : { l: 0, t: Math.min(r.bottom + 4, H * 0.6), r: 0, b: 0 };
}
function fitView(b, pad) {
  const aw = W - insets.l - insets.r, ah = H - insets.t - insets.b;
  const k = Math.min(aw / (b.x1 - b.x0 + 2 * pad), ah / (b.y1 - b.y0 + 2 * pad));
  return centred((b.x0 + b.x1) / 2, (b.y0 + b.y1) / 2, k);
}
/* view that puts map point (x, y) in the middle of the *visible* area at zoom k */
function centred(x, y, k) {
  return { x: x - (insets.l - insets.r) / 2 / k, y: y - (insets.t - insets.b) / 2 / k, k };
}
/* keep the zoom in range and the map on screen: you can never pan off into empty paper */
function clampView(v) {
  v.k = clamp(v.k, kMin, K_MAX);
  const hw = (W - insets.l - insets.r) / 2 / v.k * 0.55, hh = (H - insets.t - insets.b) / 2 / v.k * 0.55;
  const cx = (bounds.x0 + bounds.x1) / 2, cy = (bounds.y0 + bounds.y1) / 2;
  const rx = Math.max(0, (bounds.x1 - bounds.x0) / 2 - hw), ry = Math.max(0, (bounds.y1 - bounds.y0) / 2 - hh);
  const ox = (insets.l - insets.r) / 2 / v.k, oy = (insets.t - insets.b) / 2 / v.k;   // panel offset
  v.x = clamp(v.x + ox, cx - rx, cx + rx) - ox;
  v.y = clamp(v.y + oy, cy - ry, cy + ry) - oy;
  return v;
}
const toMap = (sx, sy) => ({ x: view.x + (sx - W / 2) / view.k, y: view.y + (sy - H / 2) / view.k });

/* ============================================================ rendering */
function paintPaper(c, k, ox, oy) {
  const w = c.canvas.width, h = c.canvas.height;
  c.setTransform(1, 0, 0, 1, 0, 0);
  c.globalAlpha = 1;
  c.fillStyle = paper;
  c.fillRect(0, 0, w, h);
  // dot grid that lives on the paper: it doubles in density as you zoom in
  let sp = 40;
  const lo = 22 * dpr;
  while (sp * k < lo) sp *= 2;
  while (sp * k >= 2 * lo) sp /= 2;
  const step = sp * k, fade = (step - lo) / lo;         // 0..1: how far into this level we are
  const r = Math.max(1, Math.round(0.9 * dpr));
  const i0 = Math.ceil(-ox / step), j0 = Math.ceil(-oy / step);
  for (let pass = 0; pass < 2; pass++) {
    const a = pass ? dotA * fade : dotA;
    if (a < 0.01) continue;
    c.fillStyle = 'rgba(' + dotRGB + ',' + a.toFixed(3) + ')';
    c.beginPath();
    for (let j = j0, y = oy + j0 * step; y < h; j++, y += step) {
      for (let i = i0, x = ox + i0 * step; x < w; i++, x += step) {
        const coarse = !(i & 1) && !(j & 1);
        if (coarse !== !pass) continue;
        c.rect(Math.round(x) - r / 2, Math.round(y) - r / 2, r, r);
      }
    }
    c.fill();
  }
}

/* Draw all strokes touching the map rect [x0,y0,x1,y1]. k = device px per map unit. */
function drawInk(c, k, ox, oy, x0, y0, x1, y1) {
  c.setTransform(1, 0, 0, 1, 0, 0);
  c.lineCap = 'round'; c.lineJoin = 'round';
  const minLW = 0.45 * dpr + 0.3, thr = 0.55;
  let drawn = 0;
  for (let bi = 0; bi < batches.length; bi++) {
    const b = batches[bi], ids = b.ids, pad = b.w;
    const bx0 = x0 - pad, by0 = y0 - pad, bx1 = x1 + pad, by1 = y1 + pad;
    let any = false;
    for (let n = 0; n < ids.length; n++) {
      const s = ids[n], q = s * 4;
      if (bb[q + 2] < bx0 || bb[q] > bx1 || bb[q + 3] < by0 || bb[q + 1] > by1) continue;
      if (!any) { c.beginPath(); any = true; }
      let a = off[s] * 2;
      const e = off[s + 1] * 2;
      let px = pts[a] * k + ox, py = pts[a + 1] * k + oy;
      if (b.dot) {
        const r = Math.max(b.w * k / 2, 0.5 * dpr);
        c.moveTo(px + r, py); c.arc(px, py, r, 0, 6.2832);
        continue;
      }
      c.moveTo(px, py);
      for (a += 2; a < e - 2; a += 2) {
        const qx = pts[a] * k + ox, qy = pts[a + 1] * k + oy;
        const dx = qx - px, dy = qy - py;
        if ((dx < 0 ? -dx : dx) + (dy < 0 ? -dy : dy) < thr) continue;   // sub-pixel step: skip
        c.lineTo(qx, qy); px = qx; py = qy; drawn++;
      }
      c.lineTo(pts[e - 2] * k + ox, pts[e - 1] * k + oy);
      drawn += 2;
    }
    if (!any) continue;
    if (b.dot) { c.fillStyle = palette[b.c]; c.fill(); }
    else {
      const lw = b.w * k;
      c.strokeStyle = palette[b.c];
      c.lineWidth = lw < minLW ? minLW : lw;
      c.globalAlpha = lw < minLW ? clamp(0.55 + 0.45 * lw / minLW, 0.55, 1) : 1;
      c.stroke();
      c.globalAlpha = 1;
    }
  }
  return drawn;
}

/* Rough number of line segments drawInk would emit for this view. */
function estimateCost(k, x0, y0, x1, y1) {
  let cost = 0;
  for (let s = 0, q = 0; s < N; s++, q += 4) {
    if (bb[q + 2] < x0 || bb[q] > x1 || bb[q + 3] < y0 || bb[q + 1] > y1) continue;
    const n = off[s + 1] - off[s];
    const span = (bb[q + 2] - bb[q] + bb[q + 3] - bb[q + 1]) * k * 1.6 + 2;
    cost += n < span ? n : span;
  }
  return cost;
}

/* --- overview bitmap: the whole map, small. Used when zoomed far out and as a
       soft placeholder under the sharp layer while moving. */
let ovBox = null, introAt = -1;
function sizeOverview() {
  const b = { x0: bounds.x0 - 40, y0: bounds.y0 - 40, x1: bounds.x1 + 40, y1: bounds.y1 + 40 };
  let k = clamp(kFit * dpr * 1.35, 0.3, 0.8);
  const maxPx = 11e6;
  const area = (b.x1 - b.x0) * (b.y1 - b.y0) * k * k;
  if (area > maxPx) k *= Math.sqrt(maxPx / area);
  kOv = k; ovBox = b;
  ov.width = Math.ceil((b.x1 - b.x0) * k); ov.height = Math.ceil((b.y1 - b.y0) * k);
}
function renderOverview() {
  octx.setTransform(1, 0, 0, 1, 0, 0);
  octx.clearRect(0, 0, ov.width, ov.height);
  drawInk(octx, kOv, -ovBox.x0 * kOv, -ovBox.y0 * kOv, ovBox.x0, ovBox.y0, ovBox.x1, ovBox.y1);
  renderMiniBg();
}
/* intro: add strokes to the overview in the order they were originally drawn */
function overviewAppend(a, b) {
  const c = octx, k = kOv, ox = -ovBox.x0 * k, oy = -ovBox.y0 * k, minLW = 0.45 * dpr + 0.3;
  c.setTransform(1, 0, 0, 1, 0, 0);
  c.lineCap = 'round'; c.lineJoin = 'round';
  for (let s = a; s < b; s++) {
    let p = off[s] * 2;
    const e = off[s + 1] * 2;
    c.beginPath();
    if (e - p === 2) {
      c.arc(pts[p] * k + ox, pts[p + 1] * k + oy, Math.max(wid[s] * k / 2, 0.5 * dpr), 0, 6.2832);
      c.fillStyle = palette[col[s]]; c.fill();
      continue;
    }
    c.moveTo(pts[p] * k + ox, pts[p + 1] * k + oy);
    for (p += 2; p < e; p += 2) c.lineTo(pts[p] * k + ox, pts[p + 1] * k + oy);
    const lw = wid[s] * k;
    c.strokeStyle = palette[col[s]];
    c.lineWidth = lw < minLW ? minLW : lw;
    c.globalAlpha = lw < minLW ? clamp(0.55 + 0.45 * lw / minLW, 0.55, 1) : 1;
    c.stroke();
  }
  c.globalAlpha = 1;
}
function blitOverview(c, k, ox, oy) {
  c.imageSmoothingEnabled = true; c.imageSmoothingQuality = 'high';
  c.drawImage(ov, ovBox.x0 * k + ox, ovBox.y0 * k + oy, (ovBox.x1 - ovBox.x0) * k, (ovBox.y1 - ovBox.y0) * k);
}

/* --- frame --- */
let snapView = null;            // the view `snap` was rendered for
let budget = 70000;             // segments we can draw per frame and stay smooth (self-tuning)
let msPerSeg = 0;
let settleTimer = 0;
let sharp = true;               // does the screen currently show a sharp frame?

function renderSharp() {
  const k = view.k * dpr, ox = W * dpr / 2 - view.x * k, oy = H * dpr / 2 - view.y * k;
  const hw = W / 2 / view.k, hh = H / 2 / view.k;
  const t0 = performance.now();
  paintPaper(sctx, k, ox, oy);
  const n = drawInk(sctx, k, ox, oy, view.x - hw, view.y - hh, view.x + hw, view.y + hh);
  const dt = performance.now() - t0;
  if (n > 4000) {
    const v = dt / n;
    msPerSeg = msPerSeg ? msPerSeg * 0.7 + v * 0.3 : v;
    budget = clamp(8 / msPerSeg, 25000, 450000);
  }
  snapView = { x: view.x, y: view.y, k: view.k };
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.drawImage(snap, 0, 0);
  sharp = true;
}

function render() {
  const k = view.k * dpr, ox = W * dpr / 2 - view.x * k, oy = H * dpr / 2 - view.y * k;
  clearTimeout(settleTimer);

  // far out (or still drawing the intro): the overview bitmap is all we need
  if (introAt >= 0 || k <= kOv * 1.12) {
    paintPaper(ctx, k, ox, oy);
    blitOverview(ctx, k, ox, oy);
    sharp = true;
    return;
  }
  const hw = W / 2 / view.k, hh = H / 2 / view.k;
  if (estimateCost(k, view.x - hw, view.y - hh, view.x + hw, view.y + hh) <= budget) { renderSharp(); return; }

  // too much ink to redraw every frame: move the last sharp frame around, sharpen when we stop
  paintPaper(ctx, k, ox, oy);
  blitOverview(ctx, k, ox, oy);
  if (snapView) {
    const r = view.k / snapView.k;
    const left = (snapView.x - W / 2 / snapView.k - view.x) * view.k + W / 2;
    const top = (snapView.y - H / 2 / snapView.k - view.y) * view.k + H / 2;
    if (r > 0.3 && r < 6 && left < W && top < H && left + W * r > 0 && top + H * r > 0) {
      ctx.imageSmoothingEnabled = true; ctx.imageSmoothingQuality = 'low';
      ctx.drawImage(snap, left * dpr, top * dpr, W * r * dpr, H * r * dpr);
    }
  }
  sharp = false;
  settleTimer = setTimeout(() => { if (!sharp) { renderSharp(); } }, 110);
}

/* ============================================================ animation */
let raf = 0, dirty = true, lastT = 0;
let fly = null;                 // camera flight {f(t) -> view, t0, dur}
let zoomTo = null;              // smooth zoom towards a screen anchor {k, sx, sy, mx, my, tau}
let glide = null;               // inertia after a drag {vx, vy}
let pulseT0 = 0;                // search-hit pulse animation start
const PULSE_MS = 2600;

function requestFrame() { if (!raf) raf = requestAnimationFrame(frame); }
function invalidate() { dirty = true; requestFrame(); }

function frame(now) {
  raf = 0;
  const dt = Math.min(now - lastT || 16, 50); lastT = now;
  let moving = false;

  if (introAt >= 0) { stepIntro(now); dirty = true; moving = introAt >= 0; }

  if (fly) {
    const t = clamp((now - fly.t0) / fly.dur, 0, 1);
    const e = t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2;
    Object.assign(view, fly.f(e));
    if (t >= 1) fly = null; else moving = true;
    dirty = true;
  }
  if (zoomTo) {
    const z = zoomTo;
    const a = 1 - Math.exp(-dt / z.tau);
    const lk = Math.log(view.k) + (Math.log(z.k) - Math.log(view.k)) * a;
    view.k = Math.exp(lk);
    if (Math.abs(Math.log(z.k) - lk) < 0.002) { view.k = z.k; zoomTo = null; } else moving = true;
    view.x = z.mx - (z.sx - W / 2) / view.k;
    view.y = z.my - (z.sy - H / 2) / view.k;
    clampView(view);
    dirty = true;
  }
  if (glide) {
    const f = Math.exp(-dt / 280);
    view.x -= glide.vx * dt / view.k; view.y -= glide.vy * dt / view.k;
    glide.vx *= f; glide.vy *= f;
    clampView(view);
    if (Math.hypot(glide.vx, glide.vy) < 0.02) glide = null; else moving = true;
    dirty = true;
  }

  const pulsing = hits.length && now - pulseT0 < PULSE_MS;
  if (dirty) {
    dirty = false;
    render();
    updateLabels();
    drawMini();
    scheduleHash();
  }
  if (dirty || pulsing || fxDirty || moving) drawFx(now);
  if (moving || pulsing) requestFrame();
}

/* van Wijk & Nuij smooth zoom-and-pan: zooms out a little on long trips, like a map app */
function zoomPath(a, b) {
  const rho = Math.SQRT2, rho2 = 2, rho4 = 4;
  const w0 = W / a.k, w1 = W / b.k, dx = b.x - a.x, dy = b.y - a.y, d2 = dx * dx + dy * dy;
  let f, S;
  if (d2 < 1e-6) {
    S = Math.log(w1 / w0) / rho;
    f = t => ({ x: a.x + t * dx, y: a.y + t * dy, k: W / (w0 * Math.exp(rho * t * S)) });
  } else {
    const d1 = Math.sqrt(d2);
    const b0 = (w1 * w1 - w0 * w0 + rho4 * d2) / (2 * w0 * rho2 * d1);
    const b1 = (w1 * w1 - w0 * w0 - rho4 * d2) / (2 * w1 * rho2 * d1);
    const r0 = Math.log(Math.sqrt(b0 * b0 + 1) - b0), r1 = Math.log(Math.sqrt(b1 * b1 + 1) - b1);
    S = (r1 - r0) / rho;
    f = t => {
      if (t >= 1) return { x: b.x, y: b.y, k: b.k };
      const s = t * S, c0 = Math.cosh(r0);
      const u = w0 / (rho2 * d1) * (c0 * Math.tanh(rho * s + r0) - Math.sinh(r0));
      return { x: a.x + u * dx, y: a.y + u * dy, k: W / (w0 * c0 / Math.cosh(rho * s + r0)) };
    };
  }
  return { f, dur: clamp(Math.abs(S) * 620, 380, 1700) };
}
function flyTo(target) {
  target = clampView(Object.assign({}, target));
  zoomTo = glide = null;
  if (reduceMotion) { Object.assign(view, target); fly = null; invalidate(); return; }
  const p = zoomPath({ x: view.x, y: view.y, k: view.k }, target);
  fly = { f: p.f, dur: p.dur, t0: performance.now() };
  lastT = fly.t0;
  requestFrame();
}
function flyToBox(b, maxK) {
  const pad = Math.max(30, Math.min(b.x1 - b.x0, b.y1 - b.y0) * 0.08);
  const v = fitView(b, pad);
  if (maxK && v.k > maxK) Object.assign(v, centred((b.x0 + b.x1) / 2, (b.y0 + b.y1) / 2, maxK));
  flyTo(v);
}
function zoomAt(sx, sy, k, tau) {
  k = clamp(k, kMin, K_MAX);
  fly = glide = null;
  const m = zoomTo ? { x: zoomTo.mx, y: zoomTo.my } : toMap(sx, sy);
  if (zoomTo && (Math.abs(zoomTo.sx - sx) > 2 || Math.abs(zoomTo.sy - sy) > 2)) Object.assign(m, toMap(sx, sy));
  if (reduceMotion) { view.k = k; view.x = m.x - (sx - W / 2) / k; view.y = m.y - (sy - H / 2) / k; clampView(view); invalidate(); return; }
  zoomTo = { k, sx, sy, mx: m.x, my: m.y, tau: tau || 70 };
  requestFrame();
}
const visibleCentre = () => ({ x: (insets.l + W - insets.r) / 2, y: (insets.t + H - insets.b) / 2 });

/* ============================================================== intro */
let introT0 = 0;
const INTRO_MS = 1900;
function startIntro() {
  if (reduceMotion) { renderOverview(); return; }
  introAt = 0; introT0 = 0;
  octx.clearRect(0, 0, ov.width, ov.height);
}
function stepIntro(now) {
  if (!introT0) introT0 = now;
  const t = clamp((now - introT0) / INTRO_MS, 0, 1);
  const upto = Math.round(N * (1 - Math.pow(1 - t, 1.6)));
  overviewAppend(introAt, upto);
  introAt = upto;
  if (t >= 1) endIntro();
}
function endIntro() {
  if (introAt < 0) return;
  overviewAppend(introAt, N);
  introAt = -1;
  renderMiniBg();
}

/* ============================================================== search */
const KIND_NAME = { title: 'Topic', node: 'Note', note: 'Note', edge: 'Connection', math: 'Formula' };
const KIND_BONUS = { title: 5, node: 2.2, note: 1, edge: 0.6, math: 0 };
const norm = s => s.toLowerCase().normalize('NFKD').replace(/[\u0300-\u036f]/g, '').replace(/[^a-z0-9]+/g, ' ').trim();
/* light stemming so "probe" finds "probing" and "policies" finds "policy" */
const SUFFIX = /(izations?|isations?|izing|ising|ized|ised|izes|ises|ize|ise|ations?|ings?|ness|ments?|ies|ed|es|ly|e|s|y)$/;
function stem(w) { if (w.length < 5) return w; const t = w.replace(SUFFIX, ''); return t.length >= 3 ? t : w; }
/* how well a single query term matches a single word of a note (0 = not at all) */
function wordScore(term, tstem, w) {
  if (w === term) return 3;
  if (w.startsWith(term)) return 2;
  if (term.length >= 4 && w.length >= 5 && stem(w) === tstem) return 1.7;
  if (term.length >= 2 && w.indexOf(term) >= 0) return 1.2;
  return 0;
}

const regions = (INDEX.regions || []).map((r, i) => ({
  id: i, name: r.name, sub: !!r.sub, color: r.color || null,
  x0: r.box[0], y0: r.box[1], x1: r.box[2], y1: r.box[3],
  ax: r.at ? r.at[0] : (r.box[0] + r.box[2]) / 2, ay: r.at ? r.at[1] : r.box[1],
  count: 0, el: null, parent: null,
}));
{ let top = null; for (const r of regions) { if (r.sub) r.parent = top; else top = r; } }
const items = (INDEX.items || []).map((a, i) => {
  const n = norm(a[0]);
  return { id: i, t: a[0], x0: a[1], y0: a[2], x1: a[3], y1: a[4], kind: a[5] || 'note', n, words: n.split(' '), region: null };
});
(function assignRegions() {
  for (const it of items) {
    const cx = (it.x0 + it.x1) / 2, cy = (it.y0 + it.y1) / 2;
    let best = null, bestArea = Infinity;
    for (const r of regions) {
      if (cx < r.x0 || cx > r.x1 || cy < r.y0 || cy > r.y1) continue;
      const area = (r.x1 - r.x0) * (r.y1 - r.y0);
      if (area < bestArea) { best = r; bestArea = area; }
    }
    it.region = best;
    if (best) { best.count++; if (best.parent) best.parent.count++; }
  }
})();

function editDistance(a, b, max) {
  if (Math.abs(a.length - b.length) > max) return max + 1;
  let prev = [], cur = [];
  for (let j = 0; j <= b.length; j++) prev[j] = j;
  for (let i = 1; i <= a.length; i++) {
    cur = [i];
    let rowMin = i;
    for (let j = 1; j <= b.length; j++) {
      cur[j] = Math.min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1));
      if (cur[j] < rowMin) rowMin = cur[j];
    }
    if (rowMin > max) return max + 1;
    prev = cur;
  }
  return prev[b.length];
}
function search(q) {
  const nq = norm(q);
  if (!nq) return [];
  const terms = nq.split(' '), stems = terms.map(stem);
  const exact = [], fuzzy = [];
  for (const it of items) {
    let score = 0, isFuzzy = false, ok = true;
    for (let ti = 0; ti < terms.length; ti++) {
      const term = terms[ti];
      let s = 0;
      for (const w of it.words) { const v = wordScore(term, stems[ti], w); if (v > s) s = v; }
      if (!s && term.length >= 4) {
        const max = term.length >= 8 ? 2 : 1;
        if (it.words.some(w => w.length >= 3 && editDistance(term, w, max) <= max)) { s = 0.5; isFuzzy = true; }
      }
      if (!s) { ok = false; break; }
      score += s;
    }
    if (!ok) continue;
    if (terms.length > 1 && it.n.indexOf(nq) >= 0) score += 4;
    if (it.n === nq) score += 6;
    score += KIND_BONUS[it.kind] || 0;
    score -= Math.min(it.n.length, 240) / 240;
    (isFuzzy ? fuzzy : exact).push({ it, score, fuzzy: isFuzzy });
  }
  const out = exact.length >= 3 ? exact : exact.concat(fuzzy);
  out.sort((a, b) => b.score - a.score || a.it.y0 - b.it.y0);
  return out;
}

const qEl = $('#q'), qClear = $('#q-clear'), qHint = $('#q-hint');
const resWrap = $('#results-wrap'), resHead = $('#results-head'), resList = $('#results'), topicsWrap = $('#topics-wrap');
let hits = [], active = -1, fxDirty = false;
const MAX_LIST = 80;

function markUp(el, text, terms) {
  const stems = terms.map(stem), re = /[A-Za-z0-9\u00c0-\u024f]+/g;
  let last = 0, m;
  while ((m = re.exec(text))) {
    const w = norm(m[0]);
    if (!w || !terms.some((t, i) => wordScore(t, stems[i], w))) continue;
    if (m.index > last) el.appendChild(document.createTextNode(text.slice(last, m.index)));
    const mk = document.createElement('mark'); mk.textContent = m[0]; el.appendChild(mk);
    last = m.index + m[0].length;
  }
  if (last < text.length) el.appendChild(document.createTextNode(text.slice(last)));
}
function runSearch(jump) {
  const q = qEl.value.trim();
  qClear.hidden = !q; qHint.hidden = !!q;
  hits = search(q); active = -1;
  resList.textContent = '';
  if (!q) { resWrap.hidden = true; topicsWrap.hidden = false; if (W <= 760) updateInsets(); fxDirty = true; requestFrame(); scheduleHash(); return; }
  resWrap.hidden = false; topicsWrap.hidden = true;
  resHead.textContent = '';
  const old = $('.empty', resWrap); if (old) old.remove();
  if (!hits.length) {
    const b = document.createElement('span'); b.textContent = 'Nothing found'; resHead.appendChild(b);
    const p = document.createElement('p'); p.className = 'empty';
    p.textContent = 'No note on the map mentions “' + q + '”. Try a shorter or different word.';
    resWrap.appendChild(p);
  } else {
    const b = document.createElement('span');
    const n = document.createElement('b'); n.textContent = hits.length;
    b.append(n, hits.length === 1 ? ' place on the map' : ' places on the map');
    const tip = document.createElement('span'); tip.textContent = '↑↓ to browse';
    resHead.append(b, tip);
    const terms = norm(q).split(' ');
    hits.slice(0, MAX_LIST).forEach((h, i) => {
      const li = document.createElement('li');
      const btn = document.createElement('button');
      btn.type = 'button'; btn.className = 'hit'; btn.setAttribute('role', 'option'); btn.setAttribute('aria-selected', 'false');
      const t = document.createElement('span'); t.className = 't';
      markUp(t, h.it.t, h.fuzzy ? [] : terms);
      const m = document.createElement('span'); m.className = 'm';
      const dot = document.createElement('i');
      if (h.it.region && h.it.region.color) dot.style.setProperty('--c', h.it.region.color);
      m.append(dot, (h.it.region ? h.it.region.name + ' · ' : '') + (KIND_NAME[h.it.kind] || 'Note') + (h.fuzzy ? ' · close match' : ''));
      btn.append(t, m);
      btn.addEventListener('click', () => select(i, true));
      li.appendChild(btn); resList.appendChild(li);
    });
  }
  if (W <= 760) updateInsets();
  if (jump && hits.length) select(0, true);
  dismissHint();
  fxDirty = true; requestFrame(); scheduleHash();
}
function select(i, go) {
  if (!hits.length) return;
  active = (i + hits.length) % hits.length;
  const btns = resList.querySelectorAll('.hit');
  btns.forEach((b, j) => b.setAttribute('aria-selected', j === active ? 'true' : 'false'));
  if (btns[active]) btns[active].scrollIntoView({ block: 'nearest' });
  if (go) { focusItem(hits[active].it); if (W <= 760 && document.activeElement === qEl) qEl.blur(); }
  pulseT0 = performance.now(); fxDirty = true; requestFrame();
}
/* zoom so an item is comfortably readable, with some of its surroundings in view */
function itemView(it) {
  const aw = W - insets.l - insets.r, ah = H - insets.t - insets.b;
  const w = it.x1 - it.x0, h = it.y1 - it.y0;
  const k = clamp(Math.min(aw * 0.3 / Math.max(w, 1), ah * 0.24 / Math.max(h, 1)), 1.1, K_READ);
  return centred((it.x0 + it.x1) / 2, (it.y0 + it.y1) / 2, k);
}
function focusItem(it) { flyTo(itemView(it)); }

let searchTimer = 0;
qEl.addEventListener('input', () => { clearTimeout(searchTimer); searchTimer = setTimeout(() => runSearch(false), 90); });
qEl.addEventListener('keydown', e => {
  if (e.key === 'ArrowDown' || e.key === 'ArrowUp') {
    e.preventDefault();
    if (hits.length) select(active < 0 ? 0 : active + (e.key === 'ArrowDown' ? 1 : -1), true);
  } else if (e.key === 'Enter') {
    e.preventDefault(); clearTimeout(searchTimer);
    if (norm(qEl.value) !== lastQuery()) runSearch(false);
    if (hits.length) select(active < 0 ? 0 : active + (e.shiftKey ? -1 : 1), true);
  } else if (e.key === 'Escape') {
    if (qEl.value) { qEl.value = ''; runSearch(false); } else qEl.blur();
  }
});
let lastQ = '';
function lastQuery() { const v = lastQ; lastQ = norm(qEl.value); return v; }
qEl.addEventListener('input', () => { lastQ = ''; });
qClear.addEventListener('click', () => { qEl.value = ''; runSearch(false); qEl.focus(); });

/* --- highlights for search hits, drawn like a yellow marker over the paper --- */
function rr(c, x, y, w, h, r) {
  r = Math.min(r, w / 2, h / 2);
  c.beginPath();
  c.moveTo(x + r, y); c.arcTo(x + w, y, x + w, y + h, r); c.arcTo(x + w, y + h, x, y + h, r);
  c.arcTo(x, y + h, x, y, r); c.arcTo(x, y, x + w, y, r); c.closePath();
}
function drawFx(now) {
  fxDirty = false;
  fctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  fctx.clearRect(0, 0, W, H);
  if (!hits.length) return;
  const k = view.k, ox = W / 2 - view.x * k, oy = H / 2 - view.y * k;
  const dark = document.documentElement.dataset.theme === 'dark';
  const padM = 5;
  for (let i = 0; i < hits.length && i < 400; i++) {
    const it = hits[i].it, on = i === active;
    let x = (it.x0 - padM) * k + ox, y = (it.y0 - padM) * k + oy, w = (it.x1 - it.x0 + 2 * padM) * k, h = (it.y1 - it.y0 + 2 * padM) * k;
    if (x > W + 40 || y > H + 40 || x + w < -40 || y + h < -40) continue;
    if (w < 14 || h < 14) {                // far out: show a pin instead of a box
      const cx = x + w / 2, cy = y + h / 2, r = on ? 6.5 : 4.5;
      fctx.beginPath(); fctx.arc(cx, cy, r, 0, 6.2832);
      fctx.fillStyle = marker; fctx.globalAlpha = on ? 1 : 0.85; fctx.fill();
      fctx.lineWidth = 1.5; fctx.strokeStyle = dark ? 'rgba(0,0,0,.55)' : 'rgba(60,42,0,.55)'; fctx.stroke();
      fctx.globalAlpha = 1;
      x = cx - r; y = cy - r; w = h = 2 * r;
    } else {
      rr(fctx, x, y, w, h, Math.min(10, 6 * Math.max(k, 0.6)));
      fctx.globalCompositeOperation = dark ? 'screen' : 'multiply';
      fctx.fillStyle = marker; fctx.globalAlpha = dark ? (on ? 0.3 : 0.16) : (on ? 0.5 : 0.26); fctx.fill();
      fctx.globalCompositeOperation = 'source-over'; fctx.globalAlpha = 1;
      if (on) { fctx.lineWidth = 2; fctx.strokeStyle = marker; fctx.stroke(); }
    }
    if (on && !reduceMotion && now - pulseT0 < PULSE_MS) {
      const t = ((now - pulseT0) % 1300) / 1300, g = 4 + t * 22;
      rr(fctx, x - g, y - g, w + 2 * g, h + 2 * g, 10 + g);
      fctx.lineWidth = 2.5 * (1 - t) + 0.5; fctx.strokeStyle = marker; fctx.globalAlpha = (1 - t) * 0.9; fctx.stroke();
      fctx.globalAlpha = 1;
    }
  }
}

/* ============================================== topics list + map labels */
function buildTopics() {
  const ul = $('#topics');
  for (const r of regions) {
    const li = document.createElement('li');
    const b = document.createElement('button');
    b.type = 'button'; b.className = 'topic' + (r.sub ? ' sub' : '');
    const dot = document.createElement('i'); if (r.color) dot.style.setProperty('--c', r.color);
    const name = document.createElement('span'); name.textContent = r.name;
    const cnt = document.createElement('small'); cnt.textContent = r.count || '';
    cnt.title = r.count + ' notes';
    b.append(dot, name, cnt);
    b.addEventListener('click', () => { flyToBox(r); if (W <= 760) $('#topics-toggle').setAttribute('aria-expanded', 'false'); });
    li.appendChild(b); ul.appendChild(li);

    const lab = document.createElement('button');
    lab.type = 'button'; lab.className = 'label' + (r.sub ? ' minor' : ''); lab.tabIndex = -1;
    const d2 = document.createElement('i'); if (r.color) d2.style.setProperty('--c', r.color);
    lab.append(d2, r.name);
    lab.addEventListener('click', () => flyToBox(r));
    labelsEl.appendChild(lab);
    r.el = lab; r.lw = 0;
  }
  if (!regions.length) topicsWrap.hidden = true;
  $('#topics-toggle').addEventListener('click', e => {
    const b = e.currentTarget; b.setAttribute('aria-expanded', b.getAttribute('aria-expanded') === 'true' ? 'false' : 'true');
  });
}
/* Typeset labels name the regions while the handwriting is too small to read;
 * they step aside as soon as you are close enough to read the real thing. */
function updateLabels() {
  const k = view.k, placed = [];
  for (const r of regions) {
    const el = r.el;
    if (!r.lw) { r.lw = el.offsetWidth; r.lh = el.offsetHeight; }
    const regionPx = (r.x1 - r.x0) * k;
    let show = introAt < 0 && (r.sub ? regionPx > 190 && regionPx < W * 0.55 : regionPx < W * 0.8) && k < 1.15;
    const x = (r.ax - view.x) * k + W / 2, y = (r.ay - view.y) * k + H / 2 - 8;
    if (show && (x < 0 || x > W || y < 0 || y - r.lh > H)) show = false;
    const bx = clamp(x - r.lw / 2, 4, Math.max(4, W - r.lw - 4));
    const box = { x0: bx, y0: y - r.lh, x1: bx + r.lw, y1: y };
    if (show) {
      for (const p of placed) if (box.x0 < p.x1 + 6 && box.x1 > p.x0 - 6 && box.y0 < p.y1 + 4 && box.y1 > p.y0 - 4) { show = false; break; }
    }
    if (show) placed.push(box);
    el.style.transform = 'translate(' + Math.round(box.x0) + 'px,' + Math.round(box.y0) + 'px)';
    el.classList.toggle('on', show);
  }
}

/* ============================================================= minimap */
const mctx = mini.getContext('2d');
const miniBg = document.createElement('canvas');
let mk = 1;
function renderMiniBg() {
  const cssW = 188, b = bounds;
  mk = cssW / (b.x1 - b.x0);
  const cssH = Math.round((b.y1 - b.y0) * mk), d = Math.min(window.devicePixelRatio || 1, 2);
  mini.width = miniBg.width = cssW * d; mini.height = miniBg.height = cssH * d;
  mini.style.height = cssH + 'px';
  const c = miniBg.getContext('2d');
  c.clearRect(0, 0, miniBg.width, miniBg.height);
  c.imageSmoothingQuality = 'high';
  c.drawImage(ov, (ovBox.x0 - b.x0) * mk * d, (ovBox.y0 - b.y0) * mk * d, (ovBox.x1 - ovBox.x0) * mk * d, (ovBox.y1 - ovBox.y0) * mk * d);
  drawMini();
}
function drawMini() {
  if (!miniBg.width) return;
  const zoomedIn = view.k > kFit * 1.5 && introAt < 0;
  minimapEl.classList.toggle('on', zoomedIn);
  if (!zoomedIn) return;
  const d = mini.width / 188;
  mctx.setTransform(1, 0, 0, 1, 0, 0);
  mctx.clearRect(0, 0, mini.width, mini.height);
  mctx.globalAlpha = 0.75; mctx.drawImage(miniBg, 0, 0); mctx.globalAlpha = 1;
  const x = (view.x - W / 2 / view.k - bounds.x0) * mk * d, y = (view.y - H / 2 / view.k - bounds.y0) * mk * d;
  const w = Math.max(W / view.k * mk * d, 5), h = Math.max(H / view.k * mk * d, 5);
  mctx.fillStyle = marker; mctx.globalAlpha = 0.3; mctx.fillRect(x, y, w, h);
  mctx.globalAlpha = 1; mctx.strokeStyle = marker; mctx.lineWidth = 1.5 * d; mctx.strokeRect(x, y, w, h);
}
function miniNav(e) {
  const r = mini.getBoundingClientRect();
  fly = zoomTo = glide = null;
  view.x = bounds.x0 + (e.clientX - r.left) / mk;
  view.y = bounds.y0 + (e.clientY - r.top) / mk;
  clampView(view); invalidate();
}
minimapEl.addEventListener('pointerdown', e => { minimapEl.setPointerCapture(e.pointerId); miniNav(e); });
minimapEl.addEventListener('pointermove', e => { if (e.buttons) miniNav(e); });

/* =============================================================== input */
const pointers = new Map();
let drag = null, pinch = null, hintGone = false;

function dismissHint() { if (!hintGone) { hintGone = true; $('#hint').classList.add('gone'); } }
function itemAt(mx, my) {
  let best = null, bestArea = Infinity;
  for (const it of items) {
    if (mx < it.x0 - 3 || mx > it.x1 + 3 || my < it.y0 - 3 || my > it.y1 + 3) continue;
    const a = (it.x1 - it.x0) * (it.y1 - it.y0);
    if (a < bestArea) { best = it; bestArea = a; }
  }
  return best;
}
/* A click dives in: onto the note under the pointer if there is one, otherwise a step closer. */
function clickTarget(sx, sy) {
  const m = toMap(sx, sy);
  const it = itemAt(m.x, m.y);
  if (it) { const v = itemView(it); if (v.k > view.k * 1.25) return { fly: v }; }
  if (view.k < K_READ * 0.8) return { zoom: Math.min(view.k * 2.4, K_READ) };
  return null;
}
stage.addEventListener('pointerdown', e => {
  if (e.target.closest('.label') || (e.pointerType === 'mouse' && e.button !== 0)) return;
  if (introAt >= 0) endIntro();
  stage.setPointerCapture(e.pointerId);
  pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
  fly = zoomTo = glide = null;
  if (pointers.size === 1) {
    drag = { x: e.clientX, y: e.clientY, sx: e.clientX, sy: e.clientY, t: e.timeStamp, moved: false, vx: 0, vy: 0, lt: e.timeStamp };
  } else if (pointers.size === 2) {
    const [a, b] = [...pointers.values()];
    pinch = { d: Math.hypot(a.x - b.x, a.y - b.y), k: view.k, m: toMap((a.x + b.x) / 2, (a.y + b.y) / 2) };
    drag = null;
  }
  if (document.activeElement === qEl && W <= 760) qEl.blur();
});
stage.addEventListener('pointermove', e => {
  const p = pointers.get(e.pointerId);
  if (!p) {                                  // just hovering: show whether a click would zoom
    if (e.pointerType === 'mouse' && !e.target.closest('.label')) stage.classList.toggle('can-zoom', !!clickTarget(e.clientX, e.clientY));
    return;
  }
  p.x = e.clientX; p.y = e.clientY;
  if (pinch && pointers.size >= 2) {
    const [a, b] = [...pointers.values()];
    const d = Math.hypot(a.x - b.x, a.y - b.y), cx = (a.x + b.x) / 2, cy = (a.y + b.y) / 2;
    view.k = clamp(pinch.k * d / pinch.d, kMin, K_MAX);
    view.x = pinch.m.x - (cx - W / 2) / view.k; view.y = pinch.m.y - (cy - H / 2) / view.k;
    clampView(view); dismissHint(); invalidate();
  } else if (drag) {
    const dx = e.clientX - drag.x, dy = e.clientY - drag.y;
    if (!drag.moved && Math.hypot(e.clientX - drag.sx, e.clientY - drag.sy) < 5) return;
    if (!drag.moved) { drag.moved = true; stage.classList.add('dragging'); dismissHint(); }
    const dt = Math.max(e.timeStamp - drag.lt, 1);
    drag.vx = drag.vx * 0.6 + (dx / dt) * 0.4; drag.vy = drag.vy * 0.6 + (dy / dt) * 0.4;
    drag.x = e.clientX; drag.y = e.clientY; drag.lt = e.timeStamp;
    view.x -= dx / view.k; view.y -= dy / view.k;
    clampView(view); invalidate();
  }
});
function pointerEnd(e) {
  if (!pointers.has(e.pointerId)) return;
  pointers.delete(e.pointerId);
  stage.classList.remove('dragging');
  if (pinch) {
    pinch = null;
    const rest = [...pointers.values()][0];
    drag = rest ? { x: rest.x, y: rest.y, sx: rest.x, sy: rest.y, t: e.timeStamp, moved: true, vx: 0, vy: 0, lt: e.timeStamp } : null;
    return;
  }
  if (!drag) return;
  const d = drag; drag = null;
  if (e.type === 'pointercancel') return;
  if (!d.moved) {
    if (e.timeStamp - d.t < 450) {
      const t = clickTarget(e.clientX, e.clientY);
      dismissHint();
      if (t && t.fly) flyTo(t.fly); else if (t) zoomAt(e.clientX, e.clientY, t.zoom, 150);
    }
  } else if (e.timeStamp - d.lt < 60 && Math.hypot(d.vx, d.vy) > 0.15 && !reduceMotion) {
    glide = { vx: d.vx, vy: d.vy }; lastT = performance.now(); requestFrame();
  }
}
stage.addEventListener('pointerup', pointerEnd);
stage.addEventListener('pointercancel', pointerEnd);
stage.addEventListener('wheel', e => {
  e.preventDefault();
  if (introAt >= 0) endIntro();
  let dy = e.deltaY;
  if (e.deltaMode === 1) dy *= 32; else if (e.deltaMode === 2) dy *= H;
  dy = clamp(dy, -260, 260);
  const base = zoomTo ? zoomTo.k : view.k;
  zoomAt(e.clientX, e.clientY, base * Math.exp(-dy * (e.ctrlKey ? 0.011 : 0.0024)), 75);
  dismissHint();
}, { passive: false });
// Safari sends its own pinch events for trackpads
let gk = 1;
stage.addEventListener('gesturestart', e => { e.preventDefault(); gk = view.k; });
stage.addEventListener('gesturechange', e => { e.preventDefault(); zoomAt(e.clientX, e.clientY, gk * e.scale, 40); });
stage.addEventListener('contextmenu', e => { if (e.target === cv || e.target === stage) e.preventDefault(); });

function zoomStep(f) { const c = visibleCentre(); zoomAt(c.x, c.y, (zoomTo ? zoomTo.k : view.k) * f, 110); }
function showAll() { flyTo(fitView(bounds, 0)); }
$('#btn-in').addEventListener('click', () => zoomStep(1.7));
$('#btn-out').addEventListener('click', () => zoomStep(1 / 1.7));
$('#btn-fit').addEventListener('click', showAll);
// the title takes you home: clear any search and fly back to the whole map
$('#home').addEventListener('click', e => {
  e.preventDefault();
  if (qEl.value) { qEl.value = ''; runSearch(false); }
  showAll();
  dismissHint();
});
$('#btn-theme').addEventListener('click', () => {
  const t = document.documentElement.dataset.theme === 'dark' ? 'light' : 'dark';
  document.documentElement.dataset.theme = t;
  try { localStorage.setItem('mind-theme', t); } catch (e) {}
  endIntro(); readTheme(); renderOverview(); snapView = null; fxDirty = true; invalidate();
});

window.addEventListener('keydown', e => {
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const typing = /^(INPUT|TEXTAREA|SELECT)$/.test(document.activeElement.tagName);
  if (e.key === '/' && !typing) { e.preventDefault(); qEl.focus(); qEl.select(); return; }
  if (typing) return;
  const step = Math.min(W, H) * 0.22 / view.k;
  const pan = (dx, dy) => { e.preventDefault(); flyTo({ x: (fly ? fly.f(1).x : view.x) + dx, y: (fly ? fly.f(1).y : view.y) + dy, k: view.k }); };
  switch (e.key) {
    case '+': case '=': zoomStep(1.7); break;
    case '-': case '_': zoomStep(1 / 1.7); break;
    case '0': case 'Home': showAll(); break;
    case 'ArrowLeft': pan(-step, 0); break;
    case 'ArrowRight': pan(step, 0); break;
    case 'ArrowUp': pan(0, -step); break;
    case 'ArrowDown': pan(0, step); break;
    case 'Escape': if (qEl.value) { qEl.value = ''; runSearch(false); } break;
    default: return;
  }
  dismissHint();
});

/* =========================================================== deep links */
// #q=probing            -> opens with that search
// #@3120,2240,1.50      -> opens at that spot (x, y, zoom)
let hashTimer = 0;
function scheduleHash() {
  clearTimeout(hashTimer);
  hashTimer = setTimeout(() => {
    if (introAt >= 0 || fly || zoomTo || glide) return scheduleHash();
    const q = qEl.value.trim();
    let h = '';
    if (q) h = '#q=' + encodeURIComponent(q);
    else if (view.k > kFit * 1.08) h = '#@' + Math.round(view.x) + ',' + Math.round(view.y) + ',' + view.k.toFixed(2);
    try { history.replaceState(null, '', h || location.pathname + location.search); } catch (e) {}
  }, 500);
}
function applyHash() {
  const h = decodeURIComponent(location.hash.slice(1));
  if (h.startsWith('q=')) { qEl.value = h.slice(2); runSearch(false); if (hits.length) { active = 0; Object.assign(view, clampView(itemView(hits[0].it))); select(0, false); } return true; }
  const m = /^@(-?[\d.]+),(-?[\d.]+),([\d.]+)$/.exec(h);
  if (m) { Object.assign(view, clampView({ x: +m[1], y: +m[2], k: +m[3] })); return true; }
  return false;
}

/* ================================================================ start */
let resizeTimer = 0;
window.addEventListener('resize', () => {
  const wasFit = view.k <= kFit * 1.05;
  const oldOv = kOv;
  measure();
  if (wasFit) Object.assign(view, fitView(bounds, 0));
  clampView(view);
  for (const r of regions) r.lw = 0;
  invalidate();
  clearTimeout(resizeTimer);
  resizeTimer = setTimeout(() => {
    const want = clamp(kFit * dpr * 1.35, 0.3, 0.8);
    if (Math.abs(want - oldOv) / oldOv > 0.3) { endIntro(); sizeOverview(); renderOverview(); invalidate(); }
  }, 250);
});

function start() {
  if (matchMedia('(pointer: coarse)').matches) {
    const sp = document.querySelectorAll('#hint span');
    sp[0].textContent = 'Pinch to zoom'; sp[2].textContent = 'Tap to dive in';
  }
  decode();
  buildBatches();
  computeBounds();
  readTheme();
  buildTopics();
  measure();
  sizeOverview();
  Object.assign(view, fitView(bounds, 0));
  const deep = applyHash();
  if (deep) { renderOverview(); dismissHint(); } else startIntro();
  invalidate();
  $('#loader').classList.add('gone');
  setTimeout(dismissHint, 9000);
}
// let the "unfolding" screen paint before the (brief) decode blocks the thread
requestAnimationFrame(() => setTimeout(start, 0));

})();
