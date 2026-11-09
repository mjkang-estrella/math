// Random small m-coloured l-QT digraphs (not necessarily strong); test whether C_k(D) (k=l+1) has a kernel.
// l=2,3 are proved cases (sanity controls). Output counts and any kernel-less example.
'use strict';
const l = +process.argv[2], N = +process.argv[3], samples = +process.argv[4];
const k = l + 1;
let seed = 4242 + 31 * l + N; function rnd() { seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5; return (seed >>> 0); }
function isQT(adj) {
  const path = new Int32Array(l + 1), used = new Uint8Array(N); let ok = true;
  function dfs(d) { if (!ok) return; if (d === l) { const a = path[0], b = path[l]; if (!adj[a][b] && !adj[b][a]) ok = false; return; }
    const u = path[d]; for (let v = 0; v < N; v++) if (adj[u][v] && !used[v]) { used[v] = 1; path[d+1] = v; dfs(d+1); used[v] = 0; if (!ok) return; } }
  for (let s = 0; s < N && ok; s++) { used[s] = 1; path[0] = s; dfs(0); used[s] = 0; }
  return ok;
}
function closure(adj, col) {
  const cl = []; for (let i = 0; i < N; i++) cl.push(new Uint8Array(N));
  const used = new Uint8Array(N), cnt = new Int32Array(64);
  function dfs(s, u, nc) { for (let v = 0; v < N; v++) if (adj[u][v] && !used[v]) { const c = col[u][v]; const add = cnt[c] ? 0 : 1; if (nc + add > k) continue; cnt[c]++; used[v] = 1; cl[s][v] = 1; dfs(s, v, nc + add); used[v] = 0; cnt[c]--; } }
  for (let s = 0; s < N; s++) { used[s] = 1; dfs(s, s, 0); used[s] = 0; }
  return cl;
}
function hasKernel(cl) {
  const out = new Int32Array(N), nb = new Int32Array(N);
  for (let u = 0; u < N; u++) for (let v = 0; v < N; v++) if (cl[u][v]) { out[u] |= 1 << v; nb[u] |= 1 << v; nb[v] |= 1 << u; }
  let found = false;
  (function rec(i, S, forb) { if (found) return; if (i === N) { for (let u = 0; u < N; u++) if (!((S >> u) & 1) && !(out[u] & S)) return; found = true; return; }
    if (!((forb >> i) & 1)) rec(i + 1, S | (1 << i), forb | nb[i]); rec(i + 1, S, forb); })(0, 0, 0);
  return found;
}
let qt = 0, longPathish = 0, bad = 0, ex = null;
for (let t = 0; t < samples; t++) {
  const adj = []; for (let i = 0; i < N; i++) adj.push(new Uint8Array(N));
  // random: start from a random order "backward tournament"-like skeleton with noise
  const perm = [...Array(N).keys()].sort(() => (rnd() & 1) - 0.5);
  const pf = rnd() % 100, pb = rnd() % 100, pd = rnd() % 30;
  for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) if (i !== j) {
    const a = perm[i], b = perm[j];
    if (j === i + 1) { if ((rnd() % 100) >= pd) adj[a][b] = 1; }
    else if (j > i + 1) { if ((rnd() % 100) < pf / 4) adj[a][b] = 1; }
    else { if ((rnd() % 100) < pb) adj[a][b] = 1; }
  }
  if (!isQT(adj)) continue; qt++;
  const m = k + 1 + (rnd() % (N - 1));
  for (let rep = 0; rep < 20; rep++) {
    const col = []; for (let u = 0; u < N; u++) { const r = new Int32Array(N); for (let v = 0; v < N; v++) r[v] = rnd() % m; col.push(r); }
    const cl = closure(adj, col);
    let miss = 0; for (let u = 0; u < N; u++) for (let v = 0; v < N; v++) if (u !== v && !cl[u][v] && !cl[v][u]) miss++;
    if (!hasKernel(cl)) { bad++; if (!ex) ex = { adj: adj.map(r => Array.from(r)), col: col.map(r => Array.from(r)) }; break; }
  }
}
console.log(JSON.stringify({ l, k, N, samples, qtAccepted: qt, kernelLess: bad, example: ex }));
