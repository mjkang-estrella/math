// Kiraly orientation condition for clutters (MathDB 388087).
// Library: blocker (exact, bitmask), exact rational fractional-vertex check,
// CSP for existence of p:C->V, q:B->V with p(X)∈X, q(Y)∈Y and
// p(X)=q(Y)=v  =>  |X∩Y|>1.
'use strict';

function popcount(x) { let c = 0; while (x) { x &= x - 1; c++; } return c; }

// minimal transversals of clutter given as array of bitmasks on n elements (n<=24)
function blocker(C, n) {
  const N = 1 << n;
  const res = [];
  // enumerate subsets by increasing size; keep transversals that contain no smaller kept one
  const bySize = [];
  for (let k = 0; k <= n; k++) bySize.push([]);
  for (let s = 0; s < N; s++) bySize[popcount(s)].push(s);
  for (let k = 0; k <= n; k++) {
    for (const s of bySize[k]) {
      let ok = true;
      for (const c of C) if ((c & s) === 0) { ok = false; break; }
      if (!ok) continue;
      for (const t of res) if ((t & s) === t) { ok = false; break; }
      if (ok) res.push(s);
    }
  }
  return res;
}

function isClutter(C) {
  for (let i = 0; i < C.length; i++) for (let j = 0; j < C.length; j++)
    if (i !== j && (C[i] & C[j]) === C[i]) return false;
  return true;
}

function bits(m, n) { const a = []; for (let i = 0; i < n; i++) if (m >> i & 1) a.push(i); return a; }

// CSP: find p,q. Returns {p,q} or null. Exact exhaustive backtracking with forward checking.
function kiraly(C, B, n, opts = {}) {
  const sets = C.concat(B);
  const m = sets.length, nc = C.length;
  // conflicts: for variable i (in C) value v, list of (j in B) such that C_i ∩ B_j = {v}
  // domain as bitmask
  const dom0 = sets.slice();
  // conflict lists per (var, value)
  const conf = new Array(m);
  for (let i = 0; i < m; i++) conf[i] = new Map();
  for (let i = 0; i < nc; i++) for (let j = 0; j < B.length; j++) {
    const x = C[i] & B[j];
    if (popcount(x) === 1) {
      const v = 31 - Math.clz32(x);
      const a = conf[i], b = conf[nc + j];
      if (!a.has(v)) a.set(v, []); a.get(v).push(nc + j);
      if (!b.has(v)) b.set(v, []); b.get(v).push(i);
    }
  }
  const dom = dom0.slice();
  const assigned = new Int32Array(m).fill(-1);
  let nodes = 0;
  const limit = opts.nodeLimit || Infinity;
  const trail = [];
  function assign(i, v) {
    // returns false on wipeout; records trail
    assigned[i] = v;
    const lst = conf[i].get(v);
    if (lst) for (const j of lst) {
      if (assigned[j] >= 0) { if (assigned[j] === v) return false; continue; }
      if (dom[j] >> v & 1) {
        trail.push(j, dom[j]);
        dom[j] &= ~(1 << v);
        if (dom[j] === 0) return false;
      }
    }
    return true;
  }
  function undo(mark) { while (trail.length > mark) { const d = trail.pop(); const j = trail.pop(); dom[j] = d; } }
  function rec(depth) {
    if (++nodes > limit) throw new Error('limit');
    // MRV
    let best = -1, bs = 99;
    for (let i = 0; i < m; i++) if (assigned[i] < 0) {
      const s = popcount(dom[i]);
      if (s < bs) { bs = s; best = i; if (s <= 1) break; }
    }
    if (best < 0) return true;
    // value order: fewest conflicts first
    const vals = bits(dom[best], n).sort((a, b) => ((conf[best].get(a) || []).length - (conf[best].get(b) || []).length));
    for (const v of vals) {
      const mark = trail.length;
      if (assign(best, v) && rec(depth + 1)) return true;
      assigned[best] = -1; undo(mark);
    }
    return false;
  }
  const ok = rec(0);
  if (!ok) return { found: false, nodes };
  return { found: true, nodes, p: Array.from(assigned.slice(0, nc)), q: Array.from(assigned.slice(nc)) };
}

function verify(C, B, p, q) {
  for (let i = 0; i < C.length; i++) if (!(C[i] >> p[i] & 1)) return false;
  for (let j = 0; j < B.length; j++) if (!(B[j] >> q[j] & 1)) return false;
  for (let i = 0; i < C.length; i++) for (let j = 0; j < B.length; j++)
    if (p[i] === q[j] && popcount(C[i] & B[j]) <= 1) return false;
  return true;
}

// ---- exact rational linear algebra (BigInt fractions) ----
function gcd(a, b) { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) { [a, b] = [b, a % b]; } return a; }
// solve M x = rhs for square integer M; returns array of [num,den] or null if singular
function solveExact(M, rhs) {
  const n = M.length;
  const A = M.map((row, i) => row.map(BigInt).concat([BigInt(rhs[i])]));
  // fraction-free Gaussian elimination (Bareiss)
  let prev = 1n; const perm = [];
  for (let k = 0; k < n; k++) {
    let piv = -1;
    for (let i = k; i < n; i++) if (A[i][k] !== 0n) { piv = i; break; }
    if (piv < 0) return null;
    [A[k], A[piv]] = [A[piv], A[k]];
    for (let i = k + 1; i < n; i++) {
      for (let j = k + 1; j <= n; j++) A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) / prev;
      A[i][k] = 0n;
    }
    prev = A[k][k];
  }
  // back substitution with fractions
  const x = new Array(n);
  for (let i = n - 1; i >= 0; i--) {
    // x_i = (A[i][n] - sum A[i][j] x_j)/A[i][i]
    let num = A[i][n], den = 1n;
    for (let j = i + 1; j < n; j++) { // num/den -= A[i][j]*x_j
      const [xn, xd] = x[j];
      num = num * xd - A[i][j] * xn * den; den = den * xd;
      const g = gcd(num, den); if (g > 1n) { num /= g; den /= g; }
    }
    den = den * A[i][i];
    if (den < 0n) { den = -den; num = -num; }
    const g = gcd(num, den); if (g > 1n) { num /= g; den /= g; }
    x[i] = [num, den];
  }
  return x;
}

module.exports = { popcount, blocker, isClutter, bits, kiraly, verify, solveExact };
