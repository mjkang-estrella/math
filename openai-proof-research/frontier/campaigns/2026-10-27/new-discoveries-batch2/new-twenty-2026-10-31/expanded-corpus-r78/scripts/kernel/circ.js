// Search: m-coloured l-quasi-transitive digraphs D (circulants on Z_N) with C_k(D) kernel-less, k=l+1.
// Definitions (Galeana-Sanchez, Llano, Montellano-Ballesteros, arXiv 1201.2712):
//  l-quasi-transitive: for distinct u0..ul with u0->u1->...->ul, (u0,ul) or (ul,u0) is an arc.
//  C_k(D): arc (u,v), u!=v, iff a directed path (distinct vertices) u~>v uses between 1 and k colours.
//  k-coloured kernel = kernel of C_k(D) (independent + absorbent).
'use strict';
const l = +process.argv[2], N0 = +process.argv[3], N1 = +process.argv[4], iters = +(process.argv[5] || 2000);
const k = l + 1;
let seed = 987654321; function rnd() { seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5; return (seed >>> 0); }
function isQT(N, adj) { // check every directed path of length l with distinct vertices
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
function dist(N, adj) { // BFS all pairs
  const D = []; for (let s = 0; s < N; s++) { const d = new Int32Array(N).fill(-1); d[s] = 0; const q = [s];
    for (let h = 0; h < q.length; h++) { const u = q[h]; for (let v = 0; v < N; v++) if (adj[u][v] && d[v] < 0) { d[v] = d[u] + 1; q.push(v); } } D.push(d); }
  return D;
}
function closure(N, adj, col) { // col[u][v] colour; returns cl[u][v] boolean
  const cl = []; for (let i = 0; i < N; i++) cl.push(new Uint8Array(N));
  const used = new Uint8Array(N); const cnt = new Int32Array(64);
  function dfs(s, u, nc) {
    for (let v = 0; v < N; v++) if (adj[u][v] && !used[v]) {
      const c = col[u][v]; const add = cnt[c] === 0 ? 1 : 0; if (nc + add > k) continue;
      cnt[c]++; used[v] = 1; cl[s][v] = 1; dfs(s, v, nc + add); used[v] = 0; cnt[c]--;
    }
  }
  for (let s = 0; s < N; s++) { used[s] = 1; dfs(s, s, 0); used[s] = 0; }
  return cl;
}
function hasKernel(N, cl) { // brute force over independent sets, absorbing check
  const out = new Int32Array(N), into = new Int32Array(N);
  for (let u = 0; u < N; u++) for (let v = 0; v < N; v++) if (cl[u][v]) { out[u] |= 1 << v; }
  const nb = new Int32Array(N); for (let u = 0; u < N; u++) { let m = out[u]; for (let v = 0; v < N; v++) if (cl[v][u]) m |= 1 << v; nb[u] = m; }
  const full = (1 << N) - 1;
  // search independent sets S (no closure arc inside) such that every u not in S has out[u] & S
  let found = false;
  function rec(i, S, forb) {
    if (found) return;
    if (i === N) { for (let u = 0; u < N; u++) if (!((S >> u) & 1) && !(out[u] & S)) return; found = true; return; }
    if (!((forb >> i) & 1)) rec(i + 1, S | (1 << i), forb | nb[i]);
    rec(i + 1, S, forb);
  }
  rec(0, 0, 0); return found;
}
const results = [];
for (let N = N0; N <= N1; N++) {
  let qtCount = 0, diamCount = 0;
  for (let mask = 1; mask < (1 << (N - 1)); mask++) {
    const S = []; for (let s = 1; s < N; s++) if ((mask >> (s - 1)) & 1) S.push(s);
    if (S.length > 3) continue; // sparse circulants only (dense ones have small diameter)
    const adj = []; for (let u = 0; u < N; u++) { const r = new Uint8Array(N); for (const s of S) r[(u + s) % N] = 1; adj.push(r); }
    if (!isQT(N, adj)) continue; qtCount++;
    const D = dist(N, adj); let mx = 0; for (const r of D) for (const x of r) mx = Math.max(mx, x);
    if (mx < k + 1) continue; diamCount++;
    // random colourings with local search: objective = (has kernel ? 1 : 0); try many
    for (let it = 0; it < iters; it++) {
      const m = k + 1 + (rnd() % 4);
      const col = []; for (let u = 0; u < N; u++) { const r = new Int32Array(N); for (let v = 0; v < N; v++) if (adj[u][v]) r[v] = rnd() % m; col.push(r); }
      const cl = closure(N, adj, col);
      if (!hasKernel(N, cl)) { results.push({ N, S, m, col: col.map(r => Array.from(r)) }); break; }
    }
  }
  console.log(JSON.stringify({ l, k, N, qtCirculantsWithAtMost3Offsets: qtCount, withDiameterAtLeastKplus1: diamCount, found: results.filter(r => r.N === N).length }));
}
if (results.length) console.log('FOUND', JSON.stringify(results[0]));
