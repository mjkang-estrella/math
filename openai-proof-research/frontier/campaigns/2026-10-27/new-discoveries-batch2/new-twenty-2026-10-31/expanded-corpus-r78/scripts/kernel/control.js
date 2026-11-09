// Positive control: Theorem 5 of arXiv 1201.2712: directed cycle u0..u_{2k+1}, arcs (u_{2i},u_{2i+1}),(u_{2i+1},u_{2i+2}) colour i:
// no k-coloured kernel. Every digraph is 1-quasi-transitive, so this is also the l=1 endpoint failure of the literal statement.
'use strict';
for (const k of [2, 3, 4]) {
  const N = 2*k + 2; const adj = [], col = [];
  for (let i = 0; i < N; i++) { adj.push(new Uint8Array(N)); col.push(new Int32Array(N)); }
  for (let j = 0; j < N; j++) { adj[j][(j + 1) % N] = 1; col[j][(j + 1) % N] = Math.floor(j / 2); }
  const cl = []; for (let i = 0; i < N; i++) cl.push(new Uint8Array(N));
  const used = new Uint8Array(N), cnt = new Int32Array(64);
  function dfs(s, u, nc) { for (let v = 0; v < N; v++) if (adj[u][v] && !used[v]) { const c = col[u][v]; const add = cnt[c] ? 0 : 1; if (nc + add > k) continue; cnt[c]++; used[v] = 1; cl[s][v] = 1; dfs(s, v, nc + add); used[v] = 0; cnt[c]--; } }
  for (let s = 0; s < N; s++) { used[s] = 1; dfs(s, s, 0); used[s] = 0; }
  const out = new Int32Array(N), nb = new Int32Array(N);
  for (let u = 0; u < N; u++) for (let v = 0; v < N; v++) if (cl[u][v]) { out[u] |= 1 << v; nb[u] |= 1 << v; nb[v] |= 1 << u; }
  let found = false;
  (function rec(i, S, forb) { if (found) return; if (i === N) { for (let u = 0; u < N; u++) if (!((S >> u) & 1) && !(out[u] & S)) return; found = true; return; }
    if (!((forb >> i) & 1)) rec(i + 1, S | (1 << i), forb | nb[i]); rec(i + 1, S, forb); })(0, 0, 0);
  console.log(JSON.stringify({ k, N, colours: k + 1, hasKernel: found }));
}
