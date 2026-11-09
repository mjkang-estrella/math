// Sanity checks: known mni clutters must admit (p,q); known ideal clutters must not (Sperner direction).
'use strict';
const K = require('./kiraly.js');
const mask = (a) => a.reduce((m, i) => m | (1 << i), 0);
function circ(n, r) { const C = []; for (let i = 0; i < n; i++) { const s = []; for (let j = 0; j < r; j++) s.push((i + j) % n); C.push(mask(s)); } return C; }
function graphEdgeIndex(n) { const E = []; for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) E.push([i, j]); return E; }
function oddCyclesK(nv) {
  const E = graphEdgeIndex(nv); const idx = (a, b) => E.findIndex(e => (e[0] === Math.min(a, b) && e[1] === Math.max(a, b)));
  const res = new Set();
  // enumerate simple cycles of odd length
  function dfs(start, cur, visited, path) {
    for (let v = 0; v < nv; v++) {
      if (v === start && path.length >= 3 && path.length % 2 === 1) {
        const es = []; for (let i = 0; i < path.length; i++) es.push(idx(path[i], path[(i + 1) % path.length]));
        res.add(mask(es));
      }
      if (v > start && !(visited >> v & 1)) dfs(start, v, visited | (1 << v), path.concat([v]));
    }
  }
  for (let s = 0; s < nv; s++) dfs(s, s, 1 << s, [s]);
  return { C: [...res], n: E.length };
}
const tests = [];
tests.push({ name: 'F7', n: 7, C: [[0, 1, 3], [1, 2, 4], [2, 3, 5], [3, 4, 6], [4, 5, 0], [5, 6, 1], [6, 0, 2]].map(mask), expect: true });
for (const n of [5, 7, 9]) tests.push({ name: `C${n}^2`, n, C: circ(n, 2), expect: true });
tests.push({ name: 'C8^3', n: 8, C: circ(8, 3), expect: true });
tests.push({ name: 'C11^3', n: 11, C: circ(11, 3), expect: true });
tests.push({ name: 'J3', n: 4, C: [[1, 2, 3], [0, 1], [0, 2], [0, 3]].map(mask), expect: true });
const ok5 = oddCyclesK(5); tests.push({ name: 'OK5', n: ok5.n, C: ok5.C, expect: true });
// ideal ones
tests.push({ name: 'path', n: 3, C: [[0, 1], [1, 2]].map(mask), expect: false });
tests.push({ name: 'C4edges', n: 4, C: circ(4, 2), expect: false });
tests.push({ name: 'C6edges', n: 6, C: circ(6, 2), expect: false });
const E4 = graphEdgeIndex(4); const id4 = (a, b) => E4.findIndex(e => e[0] === a && e[1] === b);
tests.push({ name: 'Q6', n: 6, C: [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]].map(t => mask([id4(t[0], t[1]), id4(t[0], t[2]), id4(t[1], t[2])])), expect: false });
tests.push({ name: 'single', n: 2, C: [mask([0, 1])], expect: false });
tests.push({ name: 'C5^3', n: 5, C: circ(5, 3), expect: true });
let bad = 0;
for (const t of tests) {
  if (!K.isClutter(t.C)) { console.log(t.name, 'NOT CLUTTER'); bad++; continue; }
  const B = K.blocker(t.C, t.n);
  const r = K.kiraly(t.C, B, t.n);
  const v = r.found ? K.verify(t.C, B, r.p, r.q) : null;
  const pass = r.found === t.expect && (v !== false);
  if (!pass) bad++;
  console.log(`${t.name}: |C|=${t.C.length} |B|=${B.length} found=${r.found} verified=${v} nodes=${r.nodes} expect=${t.expect} ${pass ? 'PASS' : 'FAIL'}`);
}
console.log('failures', bad);
