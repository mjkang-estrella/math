// 368807 independent check (no shared code with the Python scripts).
// Input: JSON {"X": n x n matrix of "p/q" strings}. Checks with exact BigInt arithmetic:
//  1. X has zero diagonal, nonnegative entries, unit row and column sums, and every out-cut
//     sum_{i in S, j notin S} X_ij >= 1 for 2 <= |S| <= n-2.
//  2. The constraints tight at X (degree equalities, tight cuts, zero arcs) have rank n(n-1).
//  3. For every directed Hamiltonian cycle T, the constraints tight at both X and T have rank < n(n-1)-1,
//     i.e. X and T are not adjacent on P_ASEP^n.
// usage: node asep_independent.js n file.json
'use strict';
const fs = require('fs');
const n = Number(process.argv[2]); const Xs = JSON.parse(fs.readFileSync(process.argv[3])).X;
const gcd = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
const parse = (s) => { const [p, q] = s.includes('/') ? s.split('/') : [s, '1']; return [BigInt(p), BigInt(q)]; };
let D = 1n; for (const r of Xs) for (const s of r) { const [, q] = parse(s); D = D / gcd(D, q) * q; }
const X = Xs.map(r => r.map(s => { const [p, q] = parse(s); return p * (D / q); })); // integers, X/D is the point
const arcs = []; for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (i !== j) arcs.push([i, j]);
const m = arcs.length;
// constraint rows as 0/1 arrays over arcs, with right-hand side (for the point scaled by D: rhs*D)
const eqRows = [];
for (let j = 0; j < n; j++) eqRows.push(arcs.map(([a, b]) => b === j ? 1 : 0));
for (let i = 0; i < n; i++) eqRows.push(arcs.map(([a, b]) => a === i ? 1 : 0));
const ineq = []; // {row, rhs}
for (let mask = 0; mask < (1 << n); mask++) {
  const sz = mask.toString(2).split('').filter(c => c === '1').length;
  if (sz < 2 || sz > n - 2) continue;
  ineq.push({ row: arcs.map(([a, b]) => ((mask >> a) & 1) && !((mask >> b) & 1) ? 1 : 0), rhs: 1n, name: 'cut' + mask });
}
arcs.forEach((_, t) => { const r = new Array(m).fill(0); r[t] = 1; ineq.push({ row: r, rhs: 0n, name: 'arc' + t }); });
const val = (row, v) => { let s = 0n; for (let t = 0; t < m; t++) if (row[t]) s += v[t]; return s; };
const xv = arcs.map(([a, b]) => X[a][b]);
let ok = true;
for (let i = 0; i < n; i++) if (X[i][i] !== 0n) ok = false;
for (const r of eqRows) if (val(r, xv) !== D) ok = false;
const tightX = ineq.map(c => { const s = val(c.row, xv) - c.rhs * D; if (s < 0n) ok = false; return s === 0n; });
function rank(rows) {
  const M = rows.map(r => r.map(BigInt)); let rk = 0;
  for (let c = 0; c < m && rk < M.length; c++) {
    let p = -1; for (let i = rk; i < M.length; i++) if (M[i][c] !== 0n) { p = i; break; }
    if (p < 0) continue; [M[rk], M[p]] = [M[p], M[rk]];
    for (let i = rk + 1; i < M.length; i++) if (M[i][c] !== 0n) {
      const f = M[rk][c], g = M[i][c]; let h = 0n;
      for (let t = 0; t < m; t++) { M[i][t] = f * M[i][t] - g * M[rk][t]; h = gcd(h, M[i][t]); }
      if (h > 1n) for (let t = 0; t < m; t++) M[i][t] /= h;
    }
    rk++;
  }
  return rk;
}
const vrank = rank(eqRows.concat(ineq.filter((_, i) => tightX[i]).map(c => c.row)));
// all directed Hamiltonian cycles starting at node 0
const tours = []; const perm = [0]; const used = new Array(n).fill(false); used[0] = true;
(function rec() { if (perm.length === n) { tours.push(perm.slice()); return; }
  for (let v = 1; v < n; v++) if (!used[v]) { used[v] = true; perm.push(v); rec(); perm.pop(); used[v] = false; } })();
let maxr = -1, adjacent = 0; const hist = {};
for (const cyc of tours) {
  const tv = new Array(m).fill(0n); const idx = new Map(arcs.map(([a, b], t) => [a * n + b, t]));
  for (let k = 0; k < n; k++) tv[idx.get(cyc[k] * n + cyc[(k + 1) % n])] = 1n;
  const rows = eqRows.slice();
  ineq.forEach((c, i) => { if (tightX[i] && val(c.row, tv) === c.rhs) rows.push(c.row); });
  const r = rank(rows); hist[r] = (hist[r] || 0) + 1; if (r > maxr) maxr = r; if (r === m - 1) adjacent++;
}
console.log(JSON.stringify({ n, denominator: String(D), feasible: ok, tight_inequalities: tightX.filter(Boolean).length, vertex_rank: vrank, m,
  is_vertex: ok && vrank === m, tours: tours.length, adjacent_tours: adjacent, max_common_rank: maxr, rank_histogram: hist }));
