// 366914: linear realizations of {1^a, x^b, y^c}, x = y-k (arXiv:2502.00164, Conjecture 1.11).
// A linear realization: Hamiltonian path on 0..v-1 (v=a+b+c+1) whose multiset of |u-w| is exactly
// {1^a, x^b, y^c}. Exhaustive DFS (start in lower half by reflection symmetry) with a node cap.
// sweep: node linreal.js sweep ymin ymax B cap      single: node linreal.js one y k a b c cap
'use strict';
let v, len, rem, used, path, nodes, cap, capped, ord = [0, 1, 2], dirs = [-1, 1], randomized = false, seed = 12345;
function rnd() { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed / 0x80000000; } // deterministic LCG
const MOVES = [[0,-1],[0,1],[1,-1],[1,1],[2,-1],[2,1]];
function rdfs(cur, depth) {
  if (depth === v) return true;
  if (++nodes > cap) { capped = true; return false; }
  const mv = MOVES.slice(); for (let i = mv.length - 1; i > 0; i--) { const j = Math.floor(rnd() * (i + 1)); [mv[i], mv[j]] = [mv[j], mv[i]]; }
  for (const [t, s] of mv) {
    if (!rem[t]) continue; const nx = cur + s * len[t];
    if (nx < 0 || nx >= v || used[nx]) continue;
    used[nx] = 1; rem[t]--; path[depth] = nx;
    if (rdfs(nx, depth + 1)) return true;
    used[nx] = 0; rem[t]++; if (capped) return false;
  }
  return false;
}
function rsolve(y, k, a, b, c, tries, tcap) {
  v = a + b + c + 1; len = [1, y - k, y]; const oc = cap; cap = tcap;
  for (let i = 0; i < tries; i++) {
    const st = Math.floor(rnd() * v); nodes = 0; capped = false;
    used = new Uint8Array(v); path = new Int32Array(v); rem = [a, b, c]; used[st] = 1; path[0] = st;
    if (rdfs(st, 1)) { cap = oc; return { r: 1, path: Array.from(path) }; }
  }
  cap = oc; return { r: -1 };
}
function dfs(cur, depth) {
  if (depth === v) return true;
  if (++nodes > cap) { capped = true; return false; }
  for (const t of ord) {
    if (!rem[t]) continue;
    const L = len[t];
    for (const s of dirs) {
      const nx = cur + s * L;
      if (nx < 0 || nx >= v || used[nx]) continue;
      used[nx] = 1; rem[t]--; path[depth] = nx;
      if (dfs(nx, depth + 1)) return true;
      used[nx] = 0; rem[t]++;
      if (capped) return false;
    }
  }
  return false;
}
function solve(y, k, a, b, c) {
  nodes = 0; v = a + b + c + 1; len = [1, y - k, y];
  for (let st = 0; st <= ((v - 1) >> 1); st++) {
    used = new Uint8Array(v); path = new Int32Array(v);
    rem = [a, b, c]; used[st] = 1; path[0] = st; capped = false;
    if (dfs(st, 1)) return { r: 1, path: Array.from(path) };
    if (capped) return { r: -1 };
  }
  return { r: 0 };
}
function check(y, k, a, b, c, p) { // independent verification of a found path
  const vv = a + b + c + 1; if (p.length !== vv || new Set(p).size !== vv) return false;
  const cnt = new Map();
  for (let i = 0; i + 1 < vv; i++) { const d = Math.abs(p[i] - p[i + 1]); cnt.set(d, (cnt.get(d) || 0) + 1); }
  const want = new Map(); for (const [d, m] of [[1, a], [y - k, b], [y, c]]) want.set(d, (want.get(d) || 0) + m);
  if (cnt.size !== want.size) return false;
  for (const [d, m] of want) if (cnt.get(d) !== m) return false;
  return p.every(u => u >= 0 && u < vv);
}
const args = process.argv.slice(2);
if (args[0] === 'sweep') {
  const [y0, y1, B] = args.slice(1, 4).map(Number); cap = Number(args[4]);
  let inst = 0, found = 0, none = 0, capc = 0;
  for (let y = y0; y <= y1; y++) for (let k = 3; 2 * k < y; k++) {
    const x = y - k; if (x % 2 === 0 && y % 2 === 0) continue; // Theorem 1.4 covers a >= y-1
    const f = (x === 3 || (x % 2 === 0 && y % 2 === 1)) ? x + y - 2 : x + y - 1;
    for (let a = y; a < f; a++) for (let b = 1; b <= B; b++) for (let c = 1; c <= B; c++) {
      let s = solve(y, k, a, b, c); inst++;
      const ORDS = [[2,1,0],[1,2,0],[0,2,1],[2,0,1],[1,0,2]];
      for (let oi = 0; s.r === -1 && oi < 2 * ORDS.length; oi++) { ord = ORDS[oi % ORDS.length]; dirs = oi < ORDS.length ? [1, -1] : [-1, 1]; s = solve(y, k, a, b, c); }
      ord = [0, 1, 2]; dirs = [-1, 1];
      if (s.r === -1) s = rsolve(y, k, a, b, c, 400, 20000);
      if (s.r === 1) { if (!check(y, k, a, b, c, s.path)) { console.log('VERIFYFAIL', y, k, a, b, c); process.exit(1); } found++; }
      else if (s.r === 0) { none++; console.log(`NONE y=${y} k=${k} a=${a} b=${b} c=${c}`); }
      else { capc++; console.log(`CAP y=${y} k=${k} a=${a} b=${b} c=${c}`); }
    }
    console.log(`done y=${y} k=${k} window_a=[${y},${f - 1}] B=${B} instances_so_far=${inst}`);
  }
  console.log(`SUMMARY instances=${inst} found_verified=${found} none=${none} cap=${capc}`);
} else if (args[0] === 'one') {
  const [y, k, a, b, c] = args.slice(1, 6).map(Number); cap = Number(args[6]);
  const s = solve(y, k, a, b, c); console.log(JSON.stringify({ y, k, a, b, c, ...s, verified: s.r === 1 ? check(y, k, a, b, c, s.path) : null }));
}
if (args[0] === 'rand') { // node linreal.js rand y k a b c tries tcap seed
  const [y, k, a, b, c, tries, tcap, sd] = args.slice(1, 9).map(Number); seed = sd;
  const s = rsolve(y, k, a, b, c, tries, tcap);
  console.log(JSON.stringify({ y, k, a, b, c, ...s, verified: s.r === 1 ? check(y, k, a, b, c, s.path) : null }));
}
