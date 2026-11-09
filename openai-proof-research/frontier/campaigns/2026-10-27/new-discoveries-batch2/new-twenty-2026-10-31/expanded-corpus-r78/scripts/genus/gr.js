// Genus ranges of chord diagrams (Burns-Jonoska-Saito, arXiv 1410.6148, Def 2.1).
// A thickened chord diagram = orientable ribbon structure on the cubic graph
// (backbone cycle on 2n endpoints + n chords); each endpoint has 2 cyclic orders
// (= band end inside / outside). genus g = (n - b + 2)/2, b = #boundary components.
'use strict';
function faces(n, m, rot) { // m: partner array on 0..2n-1, rot: bit array
  const N = 2*n, D = 3*N; const seen = new Uint8Array(D); let b = 0;
  for (let s = 0; s < D; s++) {
    if (seen[s]) continue; b++; let d = s;
    while (!seen[d]) {
      seen[d] = 1; const v = (d/3)|0, k = d - 3*v; let w, kk;
      if (k === 0) { w = (v + N - 1) % N; kk = 1; }       // alpha
      else if (k === 1) { w = (v + 1) % N; kk = 0; }
      else { w = m[v]; kk = 2; }
      // sigma at w
      let k2;
      if (rot[w] === 0) k2 = (kk + 1) % 3; else k2 = (kk + 2) % 3;
      d = 3*w + k2;
    }
  }
  return b;
}
function range(n, m) { // exhaustive over 2^(2n-1) rotation systems (global flip symmetric)
  const N = 2*n; const rot = new Uint8Array(N); let lo = 1e9, hi = -1;
  const tot = 1 << (N - 1);
  for (let x = 0; x < tot; x++) {
    for (let i = 0; i < N - 1; i++) rot[i] = (x >> i) & 1; rot[N-1] = 0;
    const b = faces(n, m, rot); if (b < lo) lo = b; if (b > hi) hi = b;
  }
  return [(n - hi + 2)/2, (n - lo + 2)/2]; // [gmin, gmax]
}
function fromWord(w) { // w string of letters/digits, double occurrence
  const a = [...w]; const pos = {}; const m = new Int32Array(a.length);
  a.forEach((c, i) => { if (c in pos) { m[i] = pos[c]; m[pos[c]] = i; } else pos[c] = i; });
  return { n: a.length/2, m };
}
module.exports = { faces, range, fromWord };
if (require.main === module) {
  for (const w of ['11','1122','1212','123123','123132','12341342','12312345674675','123321','112233']) {
    const { n, m } = fromWord(w); console.log(w, JSON.stringify(range(n, m)));
  }
  // all linear matchings for n<=nmax: collect set of genus ranges
  const nmax = +(process.argv[2] || 7);
  for (let n = 1; n <= nmax; n++) {
    const N = 2*n, m = new Int32Array(N).fill(-1); const set = new Map(); let cnt = 0;
    (function rec() {
      let i = m.indexOf(-1);
      if (i < 0) { cnt++; const r = range(n, m); const k = r.join(','); set.set(k, (set.get(k)||0)+1); return; }
      for (let j = i+1; j < N; j++) if (m[j] < 0) { m[i] = j; m[j] = i; rec(); m[i] = -1; m[j] = -1; }
    })();
    console.log('n', n, 'matchings', cnt, 'ranges', JSON.stringify([...set.entries()].sort()));
  }
}
