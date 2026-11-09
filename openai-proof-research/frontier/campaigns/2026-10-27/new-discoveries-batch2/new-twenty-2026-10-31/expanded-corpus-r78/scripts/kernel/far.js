// Random strong l-QT digraphs with diameter l+2 built on the Wang-Zhang skeleton.
// Far digraph F: u->v iff d(v,u) = l+2. Test whether F has a directed cycle.
'use strict';
const l = +process.argv[2], samples = +process.argv[3], rmax = +(process.argv[4] || 4);
let seed = 12345 + l; function rnd() { seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5; return (seed >>> 0); }
function isQT(N, adj) {
  const path = new Int32Array(l + 1), used = new Uint8Array(N); let ok = true;
  function dfs(d) {
    if (!ok) return;
    if (d === l) { const a = path[0], b = path[l]; if (!adj[a][b] && !adj[b][a]) ok = false; return; }
    const u = path[d];
    for (let v = 0; v < N; v++) if (adj[u][v] && !used[v]) { used[v] = 1; path[d+1] = v; dfs(d+1); used[v] = 0; if (!ok) return; }
  }
  for (let s = 0; s < N && ok; s++) { used[s] = 1; path[0] = s; dfs(0); used[s] = 0; }
  return ok;
}
function dists(N, adj) {
  const D = []; for (let s = 0; s < N; s++) { const d = new Int32Array(N).fill(-1); d[s] = 0; const q = [s];
    for (let h = 0; h < q.length; h++) { const u = q[h]; for (let v = 0; v < N; v++) if (adj[u][v] && d[v] < 0) { d[v] = d[u] + 1; q.push(v); } } D.push(d); }
  return D;
}
let accepted = 0, withCycle = 0, maxFar = 0; const stats = {}; let example = null;
const P = l + 3;
for (let t = 0; t < samples; t++) {
  const r = rnd() % (rmax + 1), N = P + r;
  const adj = []; for (let i = 0; i < N; i++) adj.push(new Uint8Array(N));
  for (let i = 0; i + 1 < P; i++) { adj[i][i+1] = 1; if (rnd() & 1) adj[i+1][i] = 1; }
  for (let i = 0; i < P; i++) for (let j = i + 2; j < P; j++) adj[j][i] = 1;
  const pr = rnd() % 4; // density of extra arcs
  for (let a = 0; a < N; a++) for (let b = a + 1; b < N; b++) {
    if (a < P && b < P) continue;
    let x = rnd() % 4; if (a >= P && b >= P && x === 0 && (rnd() % 4) < 3) x = 1 + rnd() % 3; // R tends semicomplete
    if (x === 1 || x === 3) adj[a][b] = 1; if (x === 2 || x === 3) adj[b][a] = 1;
  }
  const D = dists(N, adj);
  let strong = true; for (const row of D) for (const x of row) if (x < 0) strong = false;
  if (!strong || D[0][P-1] !== l + 2) continue;
  let diam = 0; for (const row of D) for (const x of row) diam = Math.max(diam, x);
  if (diam !== l + 2) continue;
  if (!isQT(N, adj)) continue;
  accepted++;
  // far digraph and cycle detection
  const F = []; let nf = 0; for (let u = 0; u < N; u++) { F.push([]); for (let v = 0; v < N; v++) if (D[v][u] === l + 2) { F[u].push(v); nf++; } }
  maxFar = Math.max(maxFar, nf); stats[nf] = (stats[nf] || 0) + 1;
  const state = new Uint8Array(N); let cyc = false;
  function dfs(u) { state[u] = 1; for (const v of F[u]) { if (state[v] === 1) { cyc = true; } else if (state[v] === 0) dfs(v); } state[u] = 2; }
  for (let u = 0; u < N && !cyc; u++) if (!state[u]) dfs(u);
  // in-radius: exists v with max_u d(u,v) <= l+1 ?
  let inrad = 1e9; for (let v = 0; v < N; v++) { let mx = 0; for (let u = 0; u < N; u++) mx = Math.max(mx, D[u][v]); inrad = Math.min(inrad, mx); }
  // Lemma A: no vertex is both a far end and a far start
  for (let w = 0; w < N; w++) { let isEnd = false, isStart = false; for (let u = 0; u < N; u++) { if (D[u][w] === l + 2) isEnd = true; if (D[w][u] === l + 2) isStart = true; } if (isEnd && isStart) { stats.lemmaAfail = (stats.lemmaAfail || 0) + 1; if (!stats.lemmaAex) stats.lemmaAex = adj.map((row) => Array.from(row).map((x, v) => x ? v : -1).filter(v => v >= 0)); } }
  if (cyc) { withCycle++; if (!example) example = { N, arcs: adj.map((row, u) => Array.from(row).map((x, v) => x ? v : -1).filter(v => v >= 0)) }; }
  stats['inrad' + inrad] = (stats['inrad' + inrad] || 0) + 1;
}
console.log(JSON.stringify({ l, samples, accepted, withFarCycle: withCycle, maxFarPairs: maxFar, stats, example }));
