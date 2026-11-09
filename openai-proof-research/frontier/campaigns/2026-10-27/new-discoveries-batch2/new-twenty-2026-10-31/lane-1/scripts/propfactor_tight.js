// Targeted MathDB 388092 search: c = p/N with small N in {4,...,12}, bipartite multigraphs from a configuration model
// whose degrees mix multiples of N (all colours exact) with residues (one-unit freedom), to maximise tightness.
// Logs every COUNTEREXAMPLE and TIMEOUT line in full. Usage: node propfactor_tight.js seed trials budget
const [seed0, trials, budget] = process.argv.slice(2).map(Number);
let s = seed0 >>> 0 || 1;
const rnd = () => { s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0; return s / 4294967296; };
const ri = (a, b) => a + Math.floor(rnd() * (b - a + 1));
const solveSrc = require('fs').readFileSync(__dirname + '/propfactor.js', 'utf8');
const solve = new Function('budget', solveSrc.slice(solveSrc.indexOf('function solve'), solveSrc.indexOf('let timeouts')) + '; return solve;')(budget);
let to = 0, done = 0, cex = 0;
for (let t = 0; t < trials; t++) {
  const k = ri(3, 4), N = ri(Math.max(4, k), 12);
  const cuts = new Set(); while (cuts.size < k - 1) cuts.add(ri(1, N - 1));
  const cs = [...cuts].sort((x, y) => x - y), p = []; let prev = 0; for (const x of cs.concat([N])) { p.push(x - prev); prev = x; }
  const a = ri(2, 6), b = ri(2, 6);
  const pick = () => rnd() < 0.5 ? N * ri(1, 2) : ri(1, 2 * N);
  let da = Array.from({ length: a }, pick), db = Array.from({ length: b }, pick);
  let sa = da.reduce((x, y) => x + y, 0), sb = db.reduce((x, y) => x + y, 0);
  while (sa !== sb) { if (sa < sb) { da[ri(0, a - 1)]++; sa++; } else { db[ri(0, b - 1)]++; sb++; } }
  if (sa > 70) continue;
  const A = [], B = []; da.forEach((d, i) => { for (let r = 0; r < d; r++) A.push(i); }); db.forEach((d, j) => { for (let r = 0; r < d; r++) B.push(a + j); });
  for (let i = B.length - 1; i > 0; i--) { const j = Math.floor(rnd() * (i + 1)); [B[i], B[j]] = [B[j], B[i]]; }
  const E = A.map((u, i) => [u, B[i]]);
  try { if (!solve(a + b, E, p, N)) { cex++; console.log(JSON.stringify({ COUNTEREXAMPLE: true, a, b, E, p, N })); } done++; }
  catch (e) { if (e === 'budget') { to++; console.log(JSON.stringify({ TIMEOUT: true, a, b, E, p, N })); } else throw e; }
}
console.log(JSON.stringify({ finished: true, seed: seed0, trials, decided: done, timeouts: to, counterexamples: cex }));
