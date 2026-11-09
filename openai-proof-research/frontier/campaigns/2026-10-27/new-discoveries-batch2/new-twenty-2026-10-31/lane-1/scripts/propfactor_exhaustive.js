// Exhaustive small-size check for MathDB 388092: all bipartite graphs on parts a x b with edge multiplicities 0..maxmult,
// and all distinct floor/ceil patterns of c = p/G (k colours, positive parts, grid G) for degrees 1..Dmax.
// A pattern is the list over colours i and degrees d of [floor(c_i d), ceil(c_i d)]. Usage: a b maxmult k G budget
const [A, Bn, maxmult, k, G, budget] = process.argv.slice(2).map(Number);
const src = require('fs').readFileSync(__dirname + '/propfactor.js', 'utf8');
const solve = new Function('budget', src.slice(src.indexOf('function solve'), src.indexOf('let timeouts')) + '; return solve;')(budget);
const Dmax = Math.max(A, Bn) * maxmult;
const pats = new Map();
(function rec(prefix, left) {
  if (prefix.length === k - 1) { if (left >= 1) { const p = prefix.concat([left]); const key = p.map(x => { const r = []; for (let d = 1; d <= Dmax; d++) r.push(Math.floor(x * d / G), Math.ceil(x * d / G)); return r.join(','); }).join('|'); if (!pats.has(key)) pats.set(key, p); } return; }
  for (let x = 1; x <= left - (k - 1 - prefix.length); x++) rec(prefix.concat([x]), left - x);
})([], G);
const P = [...pats.values()];
const pairs = []; for (let i = 0; i < A; i++) for (let j = 0; j < Bn; j++) pairs.push([i, A + j]);
const total = (maxmult + 1) ** pairs.length;
let solved = 0, cex = 0, to = 0, graphs = 0;
for (let g = 0; g < total; g++) {
  let t = g; const E = [];
  for (const pr of pairs) { const m = t % (maxmult + 1); t = Math.floor(t / (maxmult + 1)); for (let r = 0; r < m; r++) E.push(pr); }
  if (!E.length) continue; graphs++;
  for (const p of P) {
    try { if (!solve(A + Bn, E, p, G)) { cex++; console.log(JSON.stringify({ COUNTEREXAMPLE: true, A, Bn, E, p, G })); } else solved++; }
    catch (e) { if (e === 'budget') { to++; console.log(JSON.stringify({ TIMEOUT: true, a: A, b: Bn, E, p, N: G })); } else throw e; }
  }
}
console.log(JSON.stringify({ finished: true, A, B: Bn, maxmult, k, G, patterns: P.length, graphs, solved, counterexamples: cex, timeouts: to }));
