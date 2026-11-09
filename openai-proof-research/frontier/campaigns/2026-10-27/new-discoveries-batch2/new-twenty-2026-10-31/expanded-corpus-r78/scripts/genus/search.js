// Search for chord diagrams with genus range of exactly two values [g,g+1], g>=2
// (counterexample to Burns-Jonoska-Saito Conjecture 3.2).
// Generation: all linear perfect matchings of 0..2n-1 (each chord diagram appears
// at least once), pruned when a parallel triple (sub-diagram 123321) appears, which
// by Lemma 4.4 of the source forces >=3 genera (we also re-verify that lemma
// empirically for n<=6 in validate mode). Per diagram: random rotation samples then
// exhaustive enumeration with early stop once face counts differ by >=4.
'use strict';
const { faces } = require('./gr.js');
const n = +process.argv[2], part = +(process.argv[3] || 0), parts = +(process.argv[4] || 1);
const noPrune = process.argv[5] === 'noprune'; const depth2 = process.argv[5] === 'depth2';
const N = 2*n, m = new Int32Array(N).fill(-1);
let seed = 12345 + part; function rnd() { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed; }
const rot = new Uint8Array(N);
function crosses(a, b, c, d) { // chords (a,b),(c,d) with a<b, c<d
  return (a < c && c < b && b < d) || (c < a && a < d && d < b);
}
function inside(a, b, c, d) { return a < c && d < b; } // (c,d) within arc (a,b)
function parallelTriple(i, j) { // new chord (i,j), check with all pairs of existing chords
  const ch = []; for (let p = 0; p < N; p++) if (m[p] > p && !(p === i && m[p] === j)) ch.push([p, m[p]]);
  const nc = [];
  for (const c of ch) if (!crosses(i, j, c[0], c[1])) nc.push(c);
  for (let x = 0; x < nc.length; x++) for (let y = x+1; y < nc.length; y++) {
    const A = nc[x], B = nc[y]; if (crosses(A[0], A[1], B[0], B[1])) continue;
    // three pairwise noncrossing chords: X=(i,j),A,B. side of chord (a,b): in = inside (a,b)
    const sides = (P, Q) => inside(P[0], P[1], Q[0], Q[1]) ? 1 : 0;
    const X = [i, j];
    // chord P separates Q,R iff sides differ
    if (sides(X, A) !== sides(X, B)) return true;
    if (sides(A, X) !== sides(A, B)) return true;
    if (sides(B, X) !== sides(B, A)) return true;
  }
  return false;
}
let leaves = 0, evaluated = 0, width1 = 0, exhaustiveRuns = 0; const found = []; const width1Ranges = new Map();
const tot = 1 << (N - 1);
function evaluate() {
  evaluated++;
  let lo = 1e9, hi = -1;
  for (let t = 0; t < 96; t++) {
    const x = rnd() % tot; for (let i = 0; i < N - 1; i++) rot[i] = (x >> i) & 1; rot[N-1] = 0;
    const b = faces(n, m, rot); if (b < lo) lo = b; if (b > hi) hi = b; if (hi - lo >= 4) return;
  }
  // hill climbing: maximize and minimize faces by single-vertex flips
  for (let r = 0; r < 12 && hi - lo < 4; r++) {
    for (const dir of [1, -1]) {
      for (let i = 0; i < N; i++) rot[i] = rnd() & 1;
      let cur = faces(n, m, rot), improved = true;
      while (improved) {
        improved = false;
        for (let v = 0; v < N; v++) {
          rot[v] ^= 1; const b = faces(n, m, rot);
          if ((b - cur) * dir > 0) { cur = b; improved = true; } else if (b === cur && (rnd() & 3) === 0) { cur = b; } else rot[v] ^= 1;
        }
      }
      if (cur < lo) lo = cur; if (cur > hi) hi = cur;
      if (hi - lo >= 4) return;
    }
  }
  exhaustiveRuns++;
  for (let x = 0; x < tot; x++) {
    let g = x ^ (x >> 1); for (let i = 0; i < N - 1; i++) rot[i] = (g >> i) & 1; rot[N-1] = 0;
    const b = faces(n, m, rot); if (b < lo) lo = b; if (b > hi) hi = b; if (hi - lo >= 4) return;
  }
  // width <= 1 (width 0 impossible by Lemma 4.2, still record)
  width1++; const gmin = (n - hi + 2)/2, gmax = (n - lo + 2)/2; const k = gmin + ',' + gmax;
  width1Ranges.set(k, (width1Ranges.get(k) || 0) + 1);
  if (gmin >= 2 || gmax - gmin !== 1) found.push({ m: Array.from(m), gmin, gmax });
}
let top = 0;
(function rec() {
  let i = m.indexOf(-1);
  if (i < 0) { leaves++; evaluate(); return; }
  for (let j = i+1; j < N; j++) if (m[j] < 0) {
    if (depth2 && m.filter(x => x >= 0).length === 2) { if ((top++ % parts) !== part) continue; }
    else if (!depth2 && i === 0) { if ((top++ % parts) !== part) continue; }
    m[i] = j; m[j] = i;
    if (noPrune || !parallelTriple(i, j)) rec();
    m[i] = -1; m[j] = -1;
  }
})();
console.log(JSON.stringify({ n, part, parts, noPrune, leaves, evaluated, exhaustiveRuns, width1, width1Ranges: [...width1Ranges.entries()], found }));
