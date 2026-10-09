// frankl_r2: exhaustive small-n test of the direct Courtade-Kumar/Hellinger route
// for Frankl.  For every union-closed family F on [n] (n<=5) with ground set
// exactly [n], put f = 1_F on the uniform cube, U = f(X), Y = BSC_rho(X).
// Computes I(U;Y) (nats), the accepted refined bound psi(rho r_m), the Hellinger
// loss, and the closure chi^2 bound of Proposition D in frankl-direct-r2.md.
// Floating-point evidence only.  Usage: node frankl_r2_exhaustive.mjs > out.json
const L = Math.log(2);
const H = r => { let s = 0; for (const q of [(1 + r) / 2, (1 - r) / 2]) if (q > 0) s -= q * Math.log(q); return s; };
const psi = r => L - H(r);
const psiInv = v => { let lo = 0, hi = 1; for (let k = 0; k < 80; k++) { const m = (lo + hi) / 2; if (psi(m) < v) lo = m; else hi = m; } return (lo + hi) / 2; };
const RHOS = [0.1, 0.3, 0.5, 0.7, 0.8, 0.9, 0.95, 0.99];

function wht(a) { // in-place unnormalized Walsh-Hadamard
  const N = a.length;
  for (let h = 1; h < N; h <<= 1) for (let i = 0; i < N; i += h << 1) for (let j = i; j < i + h; j++) { const x = a[j], y = a[j + h]; a[j] = x + y; a[j + h] = x - y; }
}
const popc = x => { let c = 0; while (x) { x &= x - 1; c++; } return c; };

// returns per-rho stats for Boolean table f (array of 0/1 length 2^n)
function analyse(f, n) {
  const N = 1 << n; let w = 0; for (const v of f) w += v;
  const alpha = w / N, m = 2 * alpha - 1;
  const rm = psiInv(H(m));
  const g = Float64Array.from(f, v => 2 * v - 1); wht(g); // g-hat * N
  const out = [];
  for (const rho of RHOS) {
    const t = new Float64Array(N);
    for (let S = 0; S < N; S++) t[S] = g[S] * rho ** popc(S);
    wht(t); // now t[x]*N = T_rho g(x)*N ... (unnormalized twice => factor N)
    let EH = 0, EHel = 0;
    for (let x = 0; x < N; x++) { const u = Math.max(-1, Math.min(1, t[x] / N)); EH += H(u); EHel += Math.sqrt(Math.max(0, 1 - u * u)); }
    EH /= N; EHel /= N;
    const I = H(m) - EH;
    const ck = psi(rho * rm);
    const hel = Math.sqrt(1 - m * m) - EHel, helB = 1 - Math.sqrt(1 - rho * rho);
    out.push({ rho, I, ck, ckU: psi(rho), hel, helB });
  }
  return { alpha, m, out };
}

// closure quantities: Stab_{s}(f) and mu_p(F)
function stab(f, n, s) { // Pr(f(X)=f(X')=1), X' s-correlated
  const N = 1 << n; const a = Float64Array.from(f); wht(a);
  let t = 0; for (let S = 0; S < N; S++) t += a[S] * a[S] * s ** popc(S); return t / (N * N);
}
function mu(f, n, p) { let t = 0; for (let x = 0; x < f.length; x++) if (f[x]) { const k = popc(x); t += p ** k * (1 - p) ** (n - k); } return t; }

function enumerateUC(n, cb) {
  const N = 1 << n; const fam = new Uint8Array(N);
  const rec = (s, forced) => {
    if (s === N) { cb(fam); return; }
    // include s
    const f2 = forced.slice(); for (let t = 0; t < s; t++) if (fam[t]) f2[s | t] = 1;
    fam[s] = 1; rec(s + 1, f2); fam[s] = 0;
    if (!forced[s]) rec(s + 1, forced);
  };
  rec(0, new Uint8Array(N));
}

const result = { rhos: RHOS, byN: {} };
let maxViolation = -Infinity, closureViol = -Infinity;
for (let n = 1; n <= 5; n++) {
  const N = 1 << n; let total = 0, honest = 0;
  // strata keyed by excess e = 2 dmax - |F| (capped) and alpha<1/2 flag
  const strata = {};
  let closureBeatsCK = 0, closureChecks = 0;
  enumerateUC(n, fam => {
    total++;
    let size = 0, uni = 0; const d = new Array(n).fill(0);
    for (let x = 0; x < N; x++) if (fam[x]) { size++; uni |= x; for (let i = 0; i < n; i++) if (x >> i & 1) d[i]++; }
    if (size === 0 || uni !== N - 1) return; // need ground set exactly [n] (excludes {} and {emptyset})
    honest++;
    const e = 2 * Math.max(...d) - size; // Frankl <=> e >= 0
    const { alpha, out } = analyse(fam, n);
    const key = `e=${Math.min(e, 3)}${e >= 3 ? '+' : ''}|${alpha < 0.5 ? 'a<1/2' : 'a>=1/2'}`;
    const st = strata[key] ??= { count: 0, maxRatio: RHOS.map(() => 0), argmax: RHOS.map(() => null), maxHelRatio: RHOS.map(() => 0) };
    st.count++;
    out.forEach((o, k) => {
      maxViolation = Math.max(maxViolation, o.I - o.ck);
      if (o.ck > 1e-12 && o.I / o.ck > st.maxRatio[k]) { st.maxRatio[k] = o.I / o.ck; st.argmax[k] = { size, alpha, freqs: d.map(v => v / size) }; }
      if (o.helB > 0) st.maxHelRatio[k] = Math.max(st.maxHelRatio[k], o.hel / o.helB);
      if (alpha < 1) { // Proposition D: chi^2-information bound from closure
        const s = o.rho * o.rho, stb = stab(fam, n, s), muP = mu(fam, n, (3 - s) / 4);
        closureViol = Math.max(closureViol, stb - muP);
        const chiBound = Math.log(1 + (muP - alpha * alpha) / (alpha * (1 - alpha)));
        closureChecks++; if (chiBound < o.ck - 1e-12) closureBeatsCK++;
      }
    });
  });
  result.byN[n] = { unionClosedFamilies: total, groundSetExact: honest, closureBoundBelowCK: `${closureBeatsCK}/${closureChecks} (family,rho) pairs`, strata };
}
result.maxOfI_minus_CK = maxViolation;           // must be <= 0 (accepted theorem)
result.maxOfStab_minus_mu = closureViol;         // must be <= 0 (Proposition D)

// all Boolean functions, n=4: max I/CK by weight, versus union-closed (any ground set) by weight
{
  const n = 4, N = 16; const best = {}, bestUC = {};
  for (let tab = 1; tab < (1 << N) - 1; tab++) {
    const f = Array.from({ length: N }, (_, x) => tab >> x & 1);
    let uc = true; for (let x = 0; x < N && uc; x++) if (f[x]) for (let y = 0; y < N; y++) if (f[y] && !f[x | y]) { uc = false; break; }
    const w = f.reduce((a, b) => a + b, 0); const { out } = analyse(f, n);
    const r = out.map(o => o.I / o.ck);
    best[w] = (best[w] ?? r.map(() => 0)).map((v, k) => Math.max(v, r[k]));
    if (uc) bestUC[w] = (bestUC[w] ?? r.map(() => 0)).map((v, k) => Math.max(v, r[k]));
  }
  result.n4_maxRatioByWeight = { allBoolean: best, unionClosed: bestUC };
}

// scalar check: level-one (order rho^2) content vs Reimer, alpha in (0,1/2]
{
  let worst = Infinity, at = null;
  for (let k = 1; k <= 20000; k++) {
    const a = 0.5 * k / 20000, m = 2 * a - 1, rm = psiInv(H(m));
    const lhs = (1 - a) * rm * rm / a, rhs = Math.log2(1 / a);
    if (lhs - rhs < worst) { worst = lhs - rhs; at = a; }
  }
  result.levelOneMinusReimer_min = { value: worst, at };
}
console.log(JSON.stringify(result, null, 1));
