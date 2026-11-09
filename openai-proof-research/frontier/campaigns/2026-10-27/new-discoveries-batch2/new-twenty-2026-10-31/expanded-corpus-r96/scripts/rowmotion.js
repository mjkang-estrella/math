// 341896: Hopkins arXiv:1902.07301 Conjecture 4.35 (minuscule doppelganger P-partition rowmotion).
// PP^l(P): order-preserving T: P -> {0..l}. row = tau_{p1} o ... o tau_{pn} (p1..pn a linear extension,
// so tau_{pn} is applied first), PL toggle T(p) <- min{T(x): x covers p} + max{T(x): p covers x} - T(p)
// with T(0hat)=0, T(1hat)=l. ddeg(T) = sum_{i=0}^{l-1} #max(T^{-1}{0..i}).
// For each poset we output the multiset of (orbit size, orbit ddeg sum); the conjecture for (P,Q) at l
// holds iff these multisets coincide.
// usage: node rowmotion.js PAIR params l   PAIR in {gr a b, grdual a b (trapezoid dual), quad n, h3}
'use strict';
function rect(a, b) { const el = []; for (let i = 1; i <= a; i++) for (let j = 1; j <= b; j++) el.push([i, j]); return fromZ2(el); }
function trapDao(a, b) { const el = []; for (let i = 1; i <= a; i++) for (let j = i; j <= a + b - i; j++) el.push([i, j]); return fromZ2(el); }
function fromZ2(el) {
  const key = (p) => p[0] + ',' + p[1]; const idx = new Map(el.map((p, t) => [key(p), t]));
  const up = el.map(() => []), down = el.map(() => []);
  el.forEach((p, t) => { for (const q of [[p[0] + 1, p[1]], [p[0], p[1] + 1]]) { const s = idx.get(key(q)); if (s !== undefined) { up[t].push(s); down[s].push(t); } } });
  return { n: el.length, up, down, names: el.map(key) };
}
function dual(P) { return { n: P.n, up: P.down, down: P.up, names: P.names.map(s => s + '*') }; }
function chainPoset(levels) { // levels: array of arrays of names; every element of level r covered by every element of level r+1
  const names = [].concat(...levels); const id = new Map(names.map((s, i) => [s, i]));
  const up = names.map(() => []), down = names.map(() => []);
  for (let r = 0; r + 1 < levels.length; r++) for (const x of levels[r]) for (const y of levels[r + 1]) { up[id.get(x)].push(id.get(y)); down[id.get(y)].push(id.get(x)); }
  return { n: names.length, up, down, names };
}
function linext(P) { // topological order (Kahn)
  const indeg = P.down.map(d => d.length), out = [], st = [];
  indeg.forEach((d, i) => { if (!d) st.push(i); });
  while (st.length) { const v = st.pop(); out.push(v); for (const w of P.up[v]) if (--indeg[w] === 0) st.push(w); }
  if (out.length !== P.n) throw new Error('cycle'); return out;
}
function allPP(P, l, ext) {
  const res = []; const T = new Int8Array(P.n);
  (function rec(t) {
    if (t === P.n) { res.push(Int8Array.from(T)); return; }
    const p = ext[t]; let lo = 0; for (const x of P.down[p]) if (T[x] > lo) lo = T[x];
    for (let v = lo; v <= l; v++) { T[p] = v; rec(t + 1); }
  })(0);
  return res;
}
function row(P, l, ext, T) {
  const S = Int8Array.from(T);
  for (let t = P.n - 1; t >= 0; t--) { const p = ext[t];
    let mn = l; for (const x of P.up[p]) if (S[x] < mn) mn = S[x];
    let mx = 0; for (const x of P.down[p]) if (S[x] > mx) mx = S[x];
    S[p] = mn + mx - S[p]; }
  return S;
}
function ddeg(P, l, T) {
  let s = 0;
  for (let i = 0; i < l; i++) for (let p = 0; p < P.n; p++) {
    if (T[p] > i) continue; let ismax = true; for (const q of P.up[p]) if (T[q] <= i) { ismax = false; break; }
    if (ismax) s++;
  }
  return s;
}
function orbits(P, l) {
  const ext = linext(P); const all = allPP(P, l, ext); const key = (T) => T.join(',');
  const seen = new Set(); const hist = new Map();
  for (const T0 of all) {
    const k0 = key(T0); if (seen.has(k0)) continue;
    let T = T0, size = 0, dsum = 0;
    do { seen.add(key(T)); size++; dsum += ddeg(P, l, T); T = row(P, l, ext, T); if (size > 100000) throw new Error('long orbit'); } while (key(T) !== k0);
    const h = size + ':' + dsum; hist.set(h, (hist.get(h) || 0) + 1);
  }
  return { count: all.length, hist: Object.fromEntries([...hist.entries()].sort()) };
}
function compare(P, Q, l, label) {
  const a = orbits(P, l), b = orbits(Q, l);
  const eq = a.count === b.count && JSON.stringify(a.hist) === JSON.stringify(b.hist);
  const diff = {}; for (const k of new Set([...Object.keys(a.hist), ...Object.keys(b.hist)])) if ((a.hist[k] || 0) !== (b.hist[k] || 0)) diff[k] = [a.hist[k] || 0, b.hist[k] || 0];
  console.log(JSON.stringify({ label, l, countP: a.count, countQ: b.count, equal: eq, orbitTypesP: Object.keys(a.hist).length, diff }));
}
const quadP = (n) => { const lv = []; for (let i = 1; i < n; i++) lv.push(['a' + i]); lv.push(['b', 'c']); for (let i = 1; i < n; i++) lv.push(['d' + i]); return chainPoset(lv); };
const i2 = (m) => { const lv = [['s1', 's2']]; for (let i = 1; i <= m - 2; i++) lv.push(['r' + i]); return chainPoset(lv); };
const args = process.argv.slice(2);
if (args[0] === 'example') { // Example 4.18 of the source
  const P = rect(2, 2); const ext = linext(P); const l = 3; let T = Int8Array.from([0, 0, 0, 0]);
  // find T with values (1,1)=1,(1,2)=1,(2,1)=2,(2,2)=2 per the source picture: bottom 1, left 1, right 2, top 2
  T = Int8Array.from([1, 1, 2, 2]); const orb = []; let S = T;
  do { orb.push([Array.from(S), ddeg(P, l, S)]); S = row(P, l, ext, S); } while (S.join() !== T.join() && orb.length < 50);
  console.log(JSON.stringify({ names: P.names, orbit: orb }));
} else if (args[0] === 'gr') { const [a, b, l] = args.slice(1).map(Number); compare(rect(a, b), dual(trapDao(a, b)), l, `Gr(${a},${a + b}) vs T_{${a},${a + b}} [order filter of B]`); }
else if (args[0] === 'grdao') { const [a, b, l] = args.slice(1).map(Number); compare(rect(a, b), trapDao(a, b), l, `Gr(${a},${a + b}) vs Dao T(${a},${b}) [unique minimum]`); }
else if (args[0] === 'quad') { const [n, l] = args.slice(1).map(Number); compare(quadP(n), i2(2 * n), l, `Q^{${2 * n}} vs I2(${2 * n}) [simple roots minimal]`); }
else if (args[0] === 'quaddual') { const [n, l] = args.slice(1).map(Number); compare(quadP(n), dual(i2(2 * n)), l, `Q^{${2 * n}} vs I2(${2 * n}) dual`); }
