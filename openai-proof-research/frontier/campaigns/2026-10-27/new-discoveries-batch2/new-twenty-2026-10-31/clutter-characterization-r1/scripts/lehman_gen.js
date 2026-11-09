// Generate cubic Lehman matrices with k=1 by iterated 3-rung ladder insertion
// (Mayhew–Pivotto–Royle, arXiv:1805.07576, Sec. 3.2) starting from the
// Moebius ladder (circulant C_5^3). Every output is re-checked exactly:
// B^T = A^{-1}(J+I) must be a 0/1 matrix.  Dedup by
// exact canonical form under row/column permutations (scripts/canon.js).
// Usage: node lehman_gen.js NMAX > out.json
'use strict';
const K = require('./kiraly.js');
const { canon } = require('./canon.js');
const NMAX = +process.argv[2] || 14;

function lehmanPartner(A) { // A: n x n 0/1 arrays; returns B (rows) or null
  const n = A.length;
  // B^T = A^{-1}(J+I): solve A * col = (J+I) col j  for each j
  const B = Array.from({ length: n }, () => new Array(n));
  for (let j = 0; j < n; j++) {
    const rhs = new Array(n).fill(1); rhs[j] = 2;
    const x = K.solveExact(A, rhs); if (!x) return null;
    for (let i = 0; i < n; i++) {
      const [num, den] = x[i];
      if (den !== 1n || (num !== 0n && num !== 1n)) return null;
      B[j][i] = Number(num); // B^T[i][j] = B[j][i]
    }
  }
  return B;
}

function invariant(A) {
  const n = A.length;
  let rc = A.map(() => 1), cc = A.map(() => 1);
  for (let it = 0; it < 4; it++) {
    const nr = A.map((row, i) => { const s = []; for (let j = 0; j < n; j++) if (row[j]) s.push(cc[j]); s.sort(); return JSON.stringify([rc[i], s]); });
    const nc = []; for (let j = 0; j < n; j++) { const s = []; for (let i = 0; i < n; i++) if (A[i][j]) s.push(rc[i]); s.sort(); nc.push(JSON.stringify([cc[j], s])); }
    const ur = [...new Set(nr)].sort(), uc = [...new Set(nc)].sort();
    rc = nr.map(x => ur.indexOf(x)); cc = nc.map(x => uc.indexOf(x));
  }
  // also include spectrum-ish: sorted multiset of (A A^T) row multisets
  const AAT = A.map(r1 => A.map(r2 => r1.reduce((s, x, k) => s + x * r2[k], 0)).sort().join('')).sort().join('|');
  return JSON.stringify([rc.slice().sort(), cc.slice().sort(), AAT]);
}

function insert(A, bL, wR, bR, wL) {
  // remove edges (bL,wR) and (bR,wL); add 3 black, 3 white
  const n = A.length, m = n + 3;
  const A2 = Array.from({ length: m }, (_, i) => Array.from({ length: m }, (_, j) => (i < n && j < n) ? A[i][j] : 0));
  A2[bL][wR] = 0; A2[bR][wL] = 0;
  const b0 = n, b1 = n + 1, b2 = n + 2, w0 = n, w1 = n + 1, w2 = n + 2;
  const blk = [[1, 1, 0], [1, 1, 1], [0, 1, 1]];
  for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) A2[n + i][n + j] = blk[i][j];
  A2[bL][w0] = 1; A2[bR][w2] = 1; A2[b0][wL] = 1; A2[b2][wR] = 1;
  return A2;
}

const start = []; for (let i = 0; i < 5; i++) { const r = new Array(5).fill(0); for (let j = 0; j < 3; j++) r[(i + j) % 5] = 1; start.push(r); }
let level = [start];
const out = { 5: [start] };
for (let n = 5; n + 3 <= NMAX; n += 3) {
  const seen = new Map(); const seenRaw = new Set();
  for (const A of level) {
    const edges = []; for (let b = 0; b < n; b++) for (let w = 0; w < n; w++) if (A[b][w]) edges.push([b, w]);
    for (const e of edges) for (const f of edges) {
      const [bR, wL] = e, [bL, wR] = f;
      if (bR === bL || wL === wR) continue;
      const A2 = insert(A, bL, wR, bR, wL);
      // regularity check
      if (A2.some(r => r.reduce((s, x) => s + x, 0) !== 3)) continue;
      if (seenRaw.has(A2.join('/'))) continue; seenRaw.add(A2.join('/'));
      const inv = canon(A2); if (seen.has(inv)) continue;
      const B = lehmanPartner(A2); if (!B) continue;
      seen.set(inv, A2);
    }
  }
  level = [...seen.values()];
  out[n + 3] = level;
  console.error(`n=${n + 3}: ${level.length} Lehman matrices (canonical classes, row/col permutations)`);
}
console.log(JSON.stringify(out));
