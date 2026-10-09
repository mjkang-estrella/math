// frankl_r2: (1) exact symmetric computation for the near-miss family
//   G_n = {A subset [n] : 1 notin A} ∪ {[n]}  (union-closed, ground set [n],
//   every i>=2 lies in exactly (|G_n|+1)/2 members),
// gap CK(rho) - I(rho) as n grows; (2) the codimension-k analogue G_{n,k} limit
// (subcube indicator) ratios; (3) n=5: max I/CK by weight over union-closed
// families vs over up-sets; (4) n<=5 near-threshold (e<=1, alpha<1/2, |F|>=3) argmax data, keyed by e.
// Floating point only.  Usage: node frankl_r2_nearmiss.mjs > out.json
const L = Math.log(2);
const H = r => { let s = 0; for (const q of [(1 + r) / 2, (1 - r) / 2]) if (q > 0) s -= q * Math.log(q); return s; };
const psi = r => L - H(r);
const psiInv = v => { let lo = 0, hi = 1; for (let k = 0; k < 90; k++) { const m = (lo + hi) / 2; if (psi(m) < v) lo = m; else hi = m; } return (lo + hi) / 2; };
const RHOS = [0.1, 0.3, 0.5, 0.7, 0.9, 0.99];
const res = {};

function logBinom(n, k) { let s = 0; for (let i = 1; i <= k; i++) s += Math.log(n - k + i) - Math.log(i); return s; }
// (1) G_n.  Coordinates: bit=1 means element present.  f(y)=[y_1=0] + [y=1^n].
res.Gn = [];
for (const n of [4, 6, 8, 12, 16, 20, 24, 28, 32, 36, 40]) {
  const alpha = (2 ** (n - 1) + 1) / 2 ** n, m = 2 * alpha - 1, rm = psiInv(H(m));
  const row = { n, size: 2 ** (n - 1) + 1, excessOverHalf: 1 / (2 * (2 ** (n - 1) + 1)), byRho: [] };
  for (const rho of RHOS) {
    const eps = (1 - rho) / 2; let EH = 0;
    for (const y1 of [0, 1]) for (let k = 0; k <= n - 1; k++) { // k = ones among y_2..y_n
      const ones = k + y1, zeros = n - ones;
      const pTop = Math.exp(zeros * Math.log(eps) + ones * Math.log(1 - eps));
      const Tf = (y1 === 0 ? 1 - eps : eps) + pTop;
      const w = Math.exp(logBinom(n - 1, k) - (n - 1) * L) / 2;
      EH += w * H(2 * Tf - 1);
    }
    const I = H(m) - EH, ck = psi(rho * rm);
    row.byRho.push({ rho, I, ck, gap: ck - I, gapTimes2nOverN: (ck - I) * 2 ** n / n, dictatorGap: psi(rho) - I });
  }
  res.Gn.push(row);
}

// generic cube tools
function wht(a) { const N = a.length; for (let h = 1; h < N; h <<= 1) for (let i = 0; i < N; i += h << 1) for (let j = i; j < i + h; j++) { const x = a[j], y = a[j + h]; a[j] = x + y; a[j + h] = x - y; } }
const popc = x => { let c = 0; while (x) { x &= x - 1; c++; } return c; };
function ratios(f, n) {
  const N = 1 << n; let w = 0; for (const v of f) w += v; const m = 2 * w / N - 1, rm = psiInv(H(m));
  const g = Float64Array.from(f, v => 2 * v - 1); wht(g);
  return RHOS.map(rho => { const t = new Float64Array(N); for (let S = 0; S < N; S++) t[S] = g[S] * rho ** popc(S); wht(t);
    let EH = 0; for (let x = 0; x < N; x++) EH += H(Math.max(-1, Math.min(1, t[x] / N))); return (H(m) - EH / N) / psi(rho * rm); });
}
// (2) subcube indicator of codimension k (limit of G_{n,k})
res.subcubeRatios = [1, 2, 3, 4, 5].map(k => ({ k, alpha: 2 ** -k, ratios: ratios(Array.from({ length: 1 << k }, (_, x) => +(x === 0)), k) }));

// (3),(4) n=5 union-closed vs up-sets, near-threshold argmax
function enumerateUC(n, cb) { const N = 1 << n, fam = new Uint8Array(N);
  const rec = (s, forced) => { if (s === N) { cb(fam); return; } const f2 = forced.slice(); for (let t = 0; t < s; t++) if (fam[t]) f2[s | t] = 1; fam[s] = 1; rec(s + 1, f2); fam[s] = 0; if (!forced[s]) rec(s + 1, forced); };
  rec(0, new Uint8Array(N)); }
res.n5 = { ucByWeight: {}, upsetByWeight: {} };
res.nearThreshold = {};
for (let n = 2; n <= 5; n++) {
  const N = 1 << n; let best = null;
  enumerateUC(n, fam => {
    let size = 0, uni = 0; const d = new Array(n).fill(0);
    for (let x = 0; x < N; x++) if (fam[x]) { size++; uni |= x; for (let i = 0; i < n; i++) if (x >> i & 1) d[i]++; }
    if (!size || size === N) return;
    const isUp = (() => { for (let x = 0; x < N; x++) if (fam[x]) for (let i = 0; i < n; i++) if (!fam[x | 1 << i]) return false; return true; })();
    const needRatios = n === 5 || (uni === N - 1 && 2 * Math.max(...d) - size <= 1 && size < N / 2 && size >= 3);
    if (!needRatios) return;
    const r = ratios(fam, n);
    if (n === 5) { const upd = (o) => { o[size] = (o[size] ?? r.map(() => 0)).map((v, k) => Math.max(v, r[k])); };
      upd(res.n5.ucByWeight); if (isUp) upd(res.n5.upsetByWeight); }
    const e = 2 * Math.max(...d) - size;
    if (uni === N - 1 && e <= 1 && size < N / 2 && size >= 3) { // nondegenerate near-threshold, alpha<1/2
      best ??= {}; const cur = best['e=' + e];
      if (!cur || r[2] > cur.r[2]) best['e=' + e] = { r, size, members: [...fam].flatMap((v, x) => v ? [x] : []), freqs: d.map(v => v / size) };
    }
  });
  res.nearThreshold[n] = best;
}
let eqCount = 0, total = 0, worstDiff = 0;
for (const w in res.n5.ucByWeight) { total++; const a = res.n5.ucByWeight[w], b = res.n5.upsetByWeight[w];
  const diff = b ? Math.max(...a.map((v, k) => v - b[k])) : Infinity; if (diff < 1e-12) eqCount++; worstDiff = Math.max(worstDiff, diff); }
res.n5.summary = { weights: total, weightsWhereUpsetsAttainUCmax: eqCount, maxExcessOfUCoverUpset: worstDiff };
console.log(JSON.stringify(res, null, 1));
