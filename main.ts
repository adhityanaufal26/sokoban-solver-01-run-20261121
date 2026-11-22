// Sokoban solver: room decomposition + per-room push-optimal A*.
// Plain JavaScript in a .ts file (Node 22 strips types; erasable syntax only).
// Deterministic: budgets are expansion counters, never the clock or randomness.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Directions: 0=u 1=d 2=l 3=r
const DX = [0, 0, -1, 1];
const DY = [-1, 1, 0, 0];
const DCH = ['u', 'd', 'l', 'r'];
const OPP = [1, 0, 3, 2];
const INF = 1e9;

// Deterministic work budgets (expansions). Room expansions (<=4 boxes, small
// floods, subset-DP matching) are far cheaper than whole-board expansions
// (up to 16 boxes), so the two paths carry separate budgets. Measured rates:
// ~9,500 room expansions/s, ~2,300 whole-board (16-box) expansions/s. Budgets
// below keep the worst case near 20s locally, inside the 60s wall even on a
// slower grader. Practice rooms need <=61 expansions each, so these caps
// carry orders of magnitude of headroom.
const ROOM_OPT_CAP = 60000;
const ROOM_W_CAP = 60000;
const WHOLE_OPT_CAP = 30000; // only used when boxes <= 8
const WHOLE_W_CAP = 30000;   // only used when boxes <= 8
const WHOLE_BIG_W_CAP = 12000; // boxes > 8: weighted only
const MAX_NODES = 1500000;
const BUDGET_ROOM = { left: 120000 };
const BUDGET_WHOLE = { left: 12000 };

// ---------- Parsing ----------

function parseLevel(text) {
  const lines = String(text).split(/\r?\n/);
  while (lines.length > 0 && lines[lines.length - 1] === '') lines.pop();
  const H = lines.length;
  let W = 0;
  for (const l of lines) if (l.length > W) W = l.length;
  const N = W * H;
  const wall = new Uint8Array(N).fill(1);
  const goal = new Uint8Array(N);
  const goals = [];
  const boxes = [];
  let player = -1;
  for (let y = 0; y < H; y++) {
    const line = lines[y];
    for (let x = 0; x < W; x++) {
      const c = x < line.length ? line[x] : '#';
      const idx = y * W + x;
      if (c === '#') continue;
      if (c === ' ' || c === '.' || c === '$' || c === '*' || c === '@' || c === '+') {
        wall[idx] = 0;
        if (c === '.' || c === '*' || c === '+') { goal[idx] = 1; goals.push(idx); }
        if (c === '$' || c === '*') boxes.push(idx);
        if (c === '@' || c === '+') player = idx;
      }
      // any other character: treated as wall (defensive)
    }
  }
  boxes.sort((a, b) => a - b);
  goals.sort((a, b) => a - b);
  // neighbor table: neigh[idx*4+d] = neighbor index or -1
  const neigh = new Int32Array(N * 4).fill(-1);
  for (let y = 0; y < H; y++) {
    for (let x = 0; x < W; x++) {
      const idx = y * W + x;
      for (let d = 0; d < 4; d++) {
        const nx = x + DX[d], ny = y + DY[d];
        if (nx >= 0 && nx < W && ny >= 0 && ny < H) neigh[idx * 4 + d] = ny * W + nx;
      }
    }
  }
  return { W, H, N, wall, goal, goals, boxes, player, neigh };
}

// ---------- Small helpers ----------

function isGoalCell(board, cell) { return board.goal[cell] === 1; }

function allOnGoals(board, boxes) {
  for (const b of boxes) if (!board.goal[b]) return false;
  return true;
}

// Flood fill player region; returns the region representative (min cell).
// Visited cells are marked in board._vis with board._stamp; boxes in board._box.
function floodRegion(board, boxes, start, allowedPlayer) {
  const { wall, neigh, N } = board;
  if (!board._vis) {
    board._vis = new Int32Array(N); board._box = new Int32Array(N);
    board._stack = new Int32Array(N); board._stamp = 0;
  }
  board._stamp = (board._stamp || 0) + 1;
  if (board._stamp > 1000000000) { board._vis.fill(0); board._box.fill(0); board._stamp = 1; }
  const st = board._stamp;
  const vis = board._vis, boxM = board._box;
  for (const b of boxes) boxM[b] = st;
  let rep = start;
  const stack = board._stack;
  let sp = 0;
  stack[sp++] = start;
  vis[start] = st;
  while (sp > 0) {
    const c = stack[--sp];
    if (c < rep) rep = c;
    for (let d = 0; d < 4; d++) {
      const nb = neigh[c * 4 + d];
      if (nb < 0 || vis[nb] === st) continue;
      if (wall[nb] || boxM[nb] === st) continue;
      if (allowedPlayer && !allowedPlayer[nb]) continue;
      vis[nb] = st;
      stack[sp++] = nb;
    }
  }
  return rep;
}

function regionHas(board, cell) { return board._vis[cell] === board._stamp; }

// BFS walk (no pushes) from `from` to `to` avoiding walls and boxes.
// Returns move string or null.
function walkPath(board, boxes, from, to) {
  if (from === to) return '';
  const { wall, neigh, N } = board;
  const boxSet = new Set(boxes);
  const prev = new Int32Array(N).fill(-2);
  const prevDir = new Int8Array(N);
  const q = [from];
  prev[from] = -1;
  let qi = 0;
  while (qi < q.length) {
    const c = q[qi++];
    for (let d = 0; d < 4; d++) {
      const nb = neigh[c * 4 + d];
      if (nb < 0 || prev[nb] !== -2) continue;
      if (wall[nb] || boxSet.has(nb)) continue;
      prev[nb] = c; prevDir[nb] = d;
      if (nb === to) {
        let s = '';
        let cur = to;
        while (cur !== from) { s = DCH[prevDir[cur]] + s; cur = prev[cur]; }
        return s;
      }
      q.push(nb);
    }
  }
  return null;
}

// Replay a move string on the board. Returns { legal, solved, pushes }.
function replay(board, moves) {
  const { wall, neigh } = board;
  const boxSet = new Set(board.boxes);
  let player = board.player;
  let pushes = 0;
  for (const ch of moves) {
    const d = DCH.indexOf(ch.toLowerCase());
    if (d < 0) return { legal: false, solved: false, pushes };
    const nb = neigh[player * 4 + d];
    if (nb < 0 || wall[nb]) return { legal: false, solved: false, pushes };
    if (boxSet.has(nb)) {
      const beyond = neigh[nb * 4 + d];
      if (beyond < 0 || wall[beyond] || boxSet.has(beyond)) return { legal: false, solved: false, pushes };
      boxSet.delete(nb); boxSet.add(beyond); pushes++;
    }
    player = nb;
  }
  let solved = boxSet.size === board.boxes.length;
  if (solved) for (const b of boxSet) if (!board.goal[b]) { solved = false; break; }
  return { legal: true, solved, pushes };
}

// ---------- Deadlock detection ----------

// 2x2 solid block containing `cell` (the just-moved box) with a non-goal box.
function has2x2Deadlock(board, boxes, boxSet, cell) {
  const { W, H, wall } = board;
  const x = cell % W, y = (cell / W) | 0;
  for (let oy = -1; oy <= 0; oy++) {
    for (let ox = -1; ox <= 0; ox++) {
      const tx = x + ox, ty = y + oy;
      if (tx < 0 || ty < 0 || tx + 1 >= W || ty + 1 >= H) continue;
      const cells = [ty * W + tx, ty * W + tx + 1, (ty + 1) * W + tx, (ty + 1) * W + tx + 1];
      let solid = true, badBox = false;
      for (const c of cells) {
        if (wall[c]) continue;
        if (boxSet.has(c)) { if (!board.goal[c]) badBox = true; continue; }
        solid = false; break;
      }
      if (solid && badBox) return true;
    }
  }
  return false;
}

// Simple freeze deadlock: a box is frozen when blocked on both axes by a
// wall or another frozen box. A frozen box not on a goal is a deadlock.
function hasFreezeDeadlock(board, boxes, boxSet) {
  const { wall, neigh } = board;
  const frozen = new Set();
  let changed = true;
  while (changed) {
    changed = false;
    for (const b of boxes) {
      if (frozen.has(b)) continue;
      const blocked = (d) => {
        const nb = neigh[b * 4 + d];
        return nb < 0 || wall[nb] === 1 || frozen.has(nb);
      };
      const hBlocked = blocked(2) || blocked(3);
      const vBlocked = blocked(0) || blocked(1);
      if (hBlocked && vBlocked) { frozen.add(b); changed = true; }
    }
  }
  for (const b of frozen) if (!board.goal[b]) return true;
  return false;
}

// ---------- Matching heuristics ----------

function matchingSubsetDP(boxes, goals, dist) {
  const n = boxes.length;
  const size = 1 << n;
  const dp = new Float64Array(size).fill(INF);
  dp[0] = 0;
  const pop = new Uint8Array(size);
  for (let m = 1; m < size; m++) pop[m] = pop[m >> 1] + (m & 1);
  for (let mask = 0; mask < size; mask++) {
    const base = dp[mask];
    if (base >= INF) continue;
    const k = pop[mask]; // next box to assign
    if (k >= n) continue;
    const box = boxes[k];
    for (let j = 0; j < n; j++) {
      if (mask & (1 << j)) continue;
      const c = dist[j][box];
      if (c >= INF) continue;
      const nm = mask | (1 << j);
      const v = base + c;
      if (v < dp[nm]) dp[nm] = v;
    }
  }
  return dp[size - 1];
}

// Jonker-Volgenant Hungarian, O(n^3), for larger box counts. Scratch arrays
// are module-level and reused to avoid per-call allocation.
const _hu = { u: null, v: null, p: null, way: null, minv: null, used: null, a: null, n: 0 };
function matchingHungarian(boxes, goals, dist) {
  const n = boxes.length;
  if (n === 0) return 0;
  const BIG = 1000000;
  if (_hu.n < n) {
    _hu.u = new Float64Array(n + 1); _hu.v = new Float64Array(n + 1);
    _hu.p = new Int32Array(n + 1); _hu.way = new Int32Array(n + 1);
    _hu.minv = new Float64Array(n + 1); _hu.used = new Uint8Array(n + 1);
    _hu.a = new Float64Array(n * n); _hu.n = n;
  }
  const { u, v, p, way, minv, used, a } = _hu;
  u.fill(0); v.fill(0); p.fill(0);
  for (let i = 0; i < n; i++) {
    let rowMin = INF;
    for (let j = 0; j < n; j++) {
      const c = dist[j][boxes[i]];
      a[i * n + j] = c >= INF ? BIG : c;
      if (c < rowMin) rowMin = c;
    }
    if (rowMin >= INF) return INF; // a box reaches no goal
  }
  for (let i = 1; i <= n; i++) {
    p[0] = i;
    let j0 = 0;
    minv.fill(Infinity);
    used.fill(0);
    do {
      used[j0] = 1;
      const i0 = p[j0];
      let delta = Infinity, j1 = -1;
      for (let j = 1; j <= n; j++) {
        if (used[j]) continue;
        const cur = a[(i0 - 1) * n + (j - 1)] - u[i0] - v[j];
        if (cur < minv[j]) { minv[j] = cur; way[j] = j0; }
        if (minv[j] < delta) { delta = minv[j]; j1 = j; }
      }
      for (let j = 0; j <= n; j++) {
        if (used[j]) { u[p[j]] += delta; v[j] -= delta; } else minv[j] -= delta;
      }
      j0 = j1;
    } while (p[j0] !== 0);
    do {
      const j1 = way[j0];
      p[j0] = p[j1];
      j0 = j1;
    } while (j0);
  }
  let total = 0;
  for (let j = 1; j <= n; j++) {
    if (p[j] === 0) return INF;
    total += a[(p[j] - 1) * n + (j - 1)];
    if (total >= BIG) return INF;
  }
  return total;
}

// Greedy assignment cost for weighted search with many boxes: most
// constrained box first, each to its nearest free goal. Not admissible
// (may exceed the true matching cost), so only used with weight > 1.
// Returns INF only when some box reaches no goal at all (sound prune).
function greedyCost(boxes, goals, dist) {
  const n = boxes.length;
  const used = new Uint8Array(n);
  const order = new Array(n);
  for (let i = 0; i < n; i++) {
    let m = INF;
    for (let j = 0; j < n; j++) { const c = dist[j][boxes[i]]; if (c < m) m = c; }
    if (m >= INF) return INF;
    order[i] = [m, i];
  }
  order.sort((x, y) => x[0] - y[0]);
  let total = 0;
  for (const [m, i] of order) {
    let best = INF, bj = -1;
    for (let j = 0; j < n; j++) {
      if (used[j]) continue;
      const c = dist[j][boxes[i]];
      if (c < best) { best = c; bj = j; }
    }
    if (bj < 0 || best >= INF) { total += m; continue; }
    used[bj] = 1;
    total += best;
  }
  return total;
}

function matchingCost(boxes, goals, dist, weight) {
  if (boxes.length <= 8) return matchingSubsetDP(boxes, goals, dist);
  if (weight > 1) return greedyCost(boxes, goals, dist);
  return matchingHungarian(boxes, goals, dist);
}

// ---------- Push A* solver ----------

// Solves a (sub-)board. opts:
//   goals: array of goal cells (length == boxes.length)
//   boxes: sorted start boxes
//   player: start player cell
//   allowedBox: Uint8Array of cells a box may occupy (or null = any floor)
//   allowedPlayer: Uint8Array of cells the player may occupy (or null)
//   exitCells: Uint8Array or null; if set, a goal state must let the player
//              reach one of these cells without pushing.
//   weight: heuristic weight (1 = optimal)
//   cap: max expansions
// Returns { pushes: [{from, dir}], expansions } or null.
function solvePush(board, opts) {
  const { wall, neigh, N } = board;
  const goals = opts.goals;
  const startBoxes = opts.boxes.slice().sort((a, b) => a - b);
  const allowedBox = opts.allowedBox || null;
  const allowedPlayer = opts.allowedPlayer || null;
  const exitCells = opts.exitCells || null;
  const weight = opts.weight || 1;
  const cap = opts.cap;
  const n = startBoxes.length;
  if (n === 0) return { pushes: [], expansions: 0 };
  if (n !== goals.length) return null;

  const boxOk = (c) => !wall[c] && (!allowedBox || allowedBox[c] === 1);
  const playerOk = (c) => !wall[c] && (!allowedPlayer || allowedPlayer[c] === 1);

  // Push distances: for each goal, reverse (pull) BFS over box cells.
  // Forward push: box x -> x+d needs player at x-d. Predecessors of c are
  // c-d when c-2d is a legal player cell.
  const dist = [];
  for (const g of goals) {
    const dArr = new Int32Array(N).fill(INF);
    if (!boxOk(g)) { dist.push(dArr); continue; }
    dArr[g] = 0;
    const q = [g];
    let qi = 0;
    while (qi < q.length) {
      const c = q[qi++];
      const dc = dArr[c];
      for (let d = 0; d < 4; d++) {
        const pred = neigh[c * 4 + OPP[d]]; // box was at c-d, pushed in dir d
        if (pred < 0 || dArr[pred] !== INF) continue;
        if (!boxOk(pred)) continue;
        const stand = neigh[pred * 4 + OPP[d]]; // player stood at pred-d
        if (stand < 0 || !playerOk(stand)) continue;
        dArr[pred] = dc + 1;
        q.push(pred);
      }
    }
    dist.push(dArr);
  }
  // Dead squares: cannot reach any goal.
  const dead = new Uint8Array(N);
  for (let c = 0; c < N; c++) {
    if (wall[c]) continue;
    let alive = false;
    for (let j = 0; j < n; j++) if (dist[j][c] < INF) { alive = true; break; }
    if (!alive) dead[c] = 1;
  }
  for (const b of startBoxes) if (dead[b]) return null;

  const budget = opts.budget;
  const hCache = new Map();
  const heuristic = (boxes) => {
    const key = boxes.join(',');
    let h = hCache.get(key);
    if (h === undefined) {
      h = matchingCost(boxes, goals, dist, weight);
      if (hCache.size < 3000000) hCache.set(key, h);
    }
    return h;
  };

  if (!board._vis) {
    board._vis = new Int32Array(N); board._box = new Int32Array(N);
    board._stack = new Int32Array(N); board._stamp = 0;
  }

  // Node storage
  const nodeBoxes = [];
  const nodePlayer = [];
  const nodeG = [];
  const nodeParent = [];
  const nodeFrom = [];
  const nodeDir = [];
  const bestG = new Map();

  // Binary heap ordered by (f, h, counter)
  const heapF = [], heapH = [], heapC = [], heapId = [];
  let counter = 0;
  const heapLess = (a, b) => {
    if (heapF[a] !== heapF[b]) return heapF[a] < heapF[b];
    if (heapH[a] !== heapH[b]) return heapH[a] < heapH[b];
    return heapC[a] < heapC[b];
  };
  const heapSwap = (a, b) => {
    let t;
    t = heapF[a]; heapF[a] = heapF[b]; heapF[b] = t;
    t = heapH[a]; heapH[a] = heapH[b]; heapH[b] = t;
    t = heapC[a]; heapC[a] = heapC[b]; heapC[b] = t;
    t = heapId[a]; heapId[a] = heapId[b]; heapId[b] = t;
  };
  const heapPush = (f, h, id) => {
    heapF.push(f); heapH.push(h); heapC.push(counter++); heapId.push(id);
    let i = heapF.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!heapLess(i, p)) break;
      heapSwap(i, p); i = p;
    }
  };
  const heapPop = () => {
    const top = heapId[0];
    const last = heapF.length - 1;
    heapSwap(0, last);
    heapF.pop(); heapH.pop(); heapC.pop(); heapId.pop();
    let i = 0;
    const len = heapF.length;
    for (;;) {
      const l = i * 2 + 1, r = l + 1;
      let m = i;
      if (l < len && heapLess(l, m)) m = l;
      if (r < len && heapLess(r, m)) m = r;
      if (m === i) break;
      heapSwap(i, m); i = m;
    }
    return top;
  };

  const addNode = (boxes, player, g, parent, from, dir) => {
    const id = nodeBoxes.length;
    nodeBoxes.push(boxes); nodePlayer.push(player); nodeG.push(g);
    nodeParent.push(parent); nodeFrom.push(from); nodeDir.push(dir);
    return id;
  };

  const startH = heuristic(startBoxes);
  if (startH >= INF) return null;
  const startId = addNode(startBoxes, opts.player, 0, -1, -1, -1);
  {
    const rep = floodRegion(board, startBoxes, opts.player, allowedPlayer);
    bestG.set(startBoxes.join(',') + '|' + rep, 0);
  }
  heapPush(weight * startH, startH, startId);

  let expansions = 0;
  while (heapF.length > 0) {
    if (expansions >= cap || budget.left <= 0) return null;
    const id = heapPop();
    const boxes = nodeBoxes[id];
    const player = nodePlayer[id];
    const g = nodeG[id];
    expansions++;
    budget.left--;

    const rep = floodRegion(board, boxes, player, allowedPlayer);
    // Goal test
    if (allOnGoals(board, boxes)) {
      let ok = true;
      if (exitCells) {
        ok = false;
        for (let c = 0; c < N; c++) if (exitCells[c] && regionHas(board, c)) { ok = true; break; }
      }
      if (ok) {
        const pushes = [];
        let cur = id;
        while (nodeParent[cur] >= 0) {
          pushes.push({ from: nodeFrom[cur], dir: nodeDir[cur] });
          cur = nodeParent[cur];
        }
        pushes.reverse();
        return { pushes, expansions };
      }
    }

    const boxSet = new Set(boxes);
    // Save region stamp: children floods overwrite it, but we only need
    // membership of stand cells now. Snapshot stand-reachable via a Set of
    // region cells is wasteful; instead check each stand cell BEFORE any
    // child flood by collecting candidate pushes first.
    const candidates = [];
    for (let i = 0; i < boxes.length; i++) {
      const b = boxes[i];
      for (let d = 0; d < 4; d++) {
        const stand = neigh[b * 4 + OPP[d]];
        if (stand < 0 || !regionHas(board, stand)) continue;
        const target = neigh[b * 4 + d];
        if (target < 0 || !boxOk(target) || boxSet.has(target) || dead[target]) continue;
        candidates.push({ i, b, d, target });
      }
    }

    for (const cand of candidates) {
      if (nodeBoxes.length >= MAX_NODES) return null;
      const newBoxes = boxes.slice();
      newBoxes[cand.i] = cand.target;
      newBoxes.sort((a, b) => a - b);
      const newSet = new Set(newBoxes);
      if (has2x2Deadlock(board, newBoxes, newSet, cand.target)) continue;
      if (hasFreezeDeadlock(board, newBoxes, newSet)) continue;
      const h = heuristic(newBoxes);
      if (h >= INF) continue;
      const ng = g + 1;
      const newPlayer = cand.b;
      const newRep = floodRegion(board, newBoxes, newPlayer, allowedPlayer);
      const key = newBoxes.join(',') + '|' + newRep;
      const prev = bestG.get(key);
      if (prev !== undefined && prev <= ng) continue;
      bestG.set(key, ng);
      const nid = addNode(newBoxes, newPlayer, ng, id, cand.b, cand.d);
      heapPush(ng + weight * h, h, nid);
    }
  }
  return null;
}

// ---------- Room decomposition ----------

function decompose(board) {
  const { W, H, N, wall, neigh, player, boxes, goals } = board;
  if (player < 0) return null;
  const py = (player / W) | 0;
  // Hallway: floor cells in the player's row connected horizontally to player.
  const hallway = new Uint8Array(N);
  {
    let x = player % W;
    hallway[player] = 1;
    for (let xx = x - 1; xx >= 0; xx--) { const c = py * W + xx; if (wall[c]) break; hallway[c] = 1; }
    for (let xx = x + 1; xx < W; xx++) { const c = py * W + xx; if (wall[c]) break; hallway[c] = 1; }
  }
  // Components of floor cells outside the hallway.
  const comp = new Int32Array(N).fill(-1);
  const comps = [];
  for (let c = 0; c < N; c++) {
    if (wall[c] || hallway[c] || comp[c] >= 0) continue;
    const id = comps.length;
    const cells = [];
    const stack = [c];
    comp[c] = id;
    while (stack.length) {
      const cur = stack.pop();
      cells.push(cur);
      for (let d = 0; d < 4; d++) {
        const nb = neigh[cur * 4 + d];
        if (nb < 0 || wall[nb] || hallway[nb] || comp[nb] >= 0) continue;
        comp[nb] = id;
        stack.push(nb);
      }
    }
    comps.push(cells);
  }
  const boxSetAll = new Set(boxes);
  const goalSetAll = new Set(goals);
  // No box or goal may sit in the hallway.
  for (const b of boxes) if (hallway[b]) return null;
  for (const g of goals) if (hallway[g]) return null;
  const rooms = [];
  for (const cells of comps) {
    const rBoxes = cells.filter((c) => boxSetAll.has(c)).sort((a, b) => a - b);
    const rGoals = cells.filter((c) => goalSetAll.has(c)).sort((a, b) => a - b);
    if (rBoxes.length === 0 && rGoals.length === 0) continue; // empty pocket
    if (rBoxes.length !== rGoals.length) return null;
    const cellSet = new Uint8Array(N);
    for (const c of cells) cellSet[c] = 1;
    rooms.push({ cells, cellSet, boxes: rBoxes, goals: rGoals, minCell: Math.min(...cells) });
  }
  if (rooms.length === 0) return null;
  const totalBoxes = rooms.reduce((s, r) => s + r.boxes.length, 0);
  if (totalBoxes !== boxes.length) return null;
  rooms.sort((a, b) => a.minCell - b.minCell);
  return { hallway, rooms };
}

// Can the player, standing at `playerPos` with `boxes` on the board, reach
// any hallway cell without pushing?
function canReachHallway(board, boxes, playerPos, hallway) {
  const rep = floodRegion(board, boxes, playerPos, null);
  for (let c = 0; c < board.N; c++) if (hallway[c] && regionHas(board, c)) return true;
  return false;
}

// Simulate a push list on the full board, producing the full move string.
// `boxes`/`player` are mutated copies owned by the caller. Returns string or null.
function applyPushes(board, state, pushes) {
  const { neigh } = board;
  let moves = '';
  for (const p of pushes) {
    const stand = neigh[p.from * 4 + OPP[p.dir]];
    const target = neigh[p.from * 4 + p.dir];
    if (stand < 0 || target < 0) return null;
    const walk = walkPath(board, state.boxes, state.player, stand);
    if (walk === null) return null;
    moves += walk + DCH[p.dir];
    const idx = state.boxes.indexOf(p.from);
    if (idx < 0) return null;
    state.boxes[idx] = target;
    state.boxes.sort((a, b) => a - b);
    state.player = p.from;
  }
  return moves;
}

function solveRoom(board, room, hallway, exitCells) {
  const allowedPlayer = new Uint8Array(board.N);
  for (let c = 0; c < board.N; c++) if (room.cellSet[c] || hallway[c]) allowedPlayer[c] = 1;
  const base = {
    goals: room.goals,
    boxes: room.boxes,
    player: board.player,
    allowedBox: room.cellSet,
    allowedPlayer,
    exitCells: exitCells || null,
    budget: BUDGET_ROOM,
  };
  let res = solvePush(board, { ...base, weight: 1, cap: ROOM_OPT_CAP });
  if (!res) res = solvePush(board, { ...base, weight: 3, cap: ROOM_W_CAP });
  return res;
}

function solveDecomposed(board, dec) {
  const { hallway, rooms } = dec;
  // Solve each room independently (no exit constraint first).
  const solved = [];
  for (const room of rooms) {
    const res = solveRoom(board, room, hallway, null);
    if (!res) return null;
    // Final state of this room: simulate pushes on its boxes.
    const fb = room.boxes.slice();
    let fp = board.player;
    for (const p of res.pushes) {
      const target = board.neigh[p.from * 4 + p.dir];
      const idx = fb.indexOf(p.from);
      if (idx < 0 || target < 0) return null;
      fb[idx] = target;
      fp = p.from;
    }
    fb.sort((a, b) => a - b);
    // Exit check on the full board with this room solved, others initial.
    const allBoxes = [];
    for (const r of rooms) allBoxes.push(...(r === room ? fb : r.boxes));
    const exitable = res.pushes.length === 0 ? true : canReachHallway(board, allBoxes, fp, hallway);
    solved.push({ room, pushes: res.pushes, exitable });
  }
  // Order: exitable rooms first, a non-exitable room last (player need not
  // leave the final room). If more than one is non-exitable, re-solve the
  // extras with an exit constraint.
  const nonExit = solved.filter((s) => !s.exitable);
  if (nonExit.length > 1) {
    for (let i = 0; i < nonExit.length - 1; i++) {
      const s = nonExit[i];
      const res = solveRoom(board, s.room, hallway, hallway);
      if (!res) return null;
      s.pushes = res.pushes;
      s.exitable = true;
    }
  }
  const ordered = [...solved.filter((s) => s.exitable), ...solved.filter((s) => !s.exitable)];
  const state = { boxes: board.boxes.slice(), player: board.player };
  let moves = '';
  for (const s of ordered) {
    const part = applyPushes(board, state, s.pushes);
    if (part === null) return null;
    moves += part;
  }
  return moves;
}

function solveWholeBoard(board) {
  const base = { goals: board.goals, boxes: board.boxes, player: board.player, budget: BUDGET_WHOLE };
  let res = null;
  if (board.boxes.length <= 8) {
    res = solvePush(board, { ...base, weight: 1, cap: WHOLE_OPT_CAP });
    if (!res) res = solvePush(board, { ...base, weight: 3, cap: WHOLE_W_CAP });
  } else {
    // Optimal search over >8 boxes cannot finish within budget; go straight
    // to weighted search with the greedy heuristic.
    res = solvePush(board, { ...base, weight: 3, cap: WHOLE_BIG_W_CAP });
  }
  if (!res) return null;
  const state = { boxes: board.boxes.slice(), player: board.player };
  return applyPushes(board, state, res.pushes);
}

// ---------- Top-level solve ----------

function solve(levelText) {
  const board = parseLevel(levelText);
  if (board.player < 0) return '';
  if (board.boxes.length !== board.goals.length) return '';
  if (board.boxes.length === 0) return '';
  if (allOnGoals(board, board.boxes)) return '';
  let moves = null;
  const dec = decompose(board);
  if (dec) {
    moves = solveDecomposed(board, dec);
    if (moves !== null) {
      const r = replay(board, moves);
      if (r.legal && r.solved) return moves;
      moves = null;
    }
  }
  moves = solveWholeBoard(board);
  if (moves !== null) {
    const r = replay(board, moves);
    if (r.legal && r.solved) return moves;
  }
  return '';
}

// ---------- Main ----------

for (const id of readdirSync(I).sort()) {
  let moves = '';
  try {
    moves = solve(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  } catch (e) {
    moves = '';
  }
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
