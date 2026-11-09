// For each Lehman matrix A (and A^T) from a generator JSON, treat rows as clutter edges,
// compute exact blocker, test Kiraly (p,q) existence; verify any witness.
'use strict';
const fs = require('fs'); const K = require('./kiraly.js');
const data = JSON.parse(fs.readFileSync(process.argv[2]));
const T = (A) => A[0].map((_, j) => A.map(r => r[j]));
const toMasks = (A) => A.map(r => r.reduce((m, x, j) => m | (x << j), 0));
let fails = 0, total = 0;
for (const n of Object.keys(data)) data[n].forEach((A, idx) => {
  for (const [lab, M] of [['A', A], ['AT', T(A)]]) {
    const C = toMasks(M), nn = M.length;
    const B = K.blocker(C, nn);
    const minB = Math.min(...B.map(K.popcount));
    const r = K.kiraly(C, B, nn);
    const v = r.found ? K.verify(C, B, r.p, r.q) : null;
    total++; if (!r.found || !v) fails++;
    console.log(`n=${n} #${idx} ${lab}: |C|=${C.length} |B|=${B.length} s=${minB} coreB=${B.filter(b => K.popcount(b) === minB).length} found=${r.found} verified=${v} nodes=${r.nodes}`);
  }
});
console.log(`total=${total} no-witness-or-unverified=${fails}`);
