// MathDB 388036, case k=l=2: search for capacitated digraph (root 0, c in {0,1,2}, no parallel arcs) that is
// rooted 4-arc-connected w.r.t. c (Edmonds => 4 arborescences pack) but whose arcs cannot be split into two
// sides (c=2 arcs on both sides WLOG, c=1 arcs on one side) each rooted 2-arc-connected (=> contains a 2-arborescence).
// Arcs entering the root are omitted (never useful). Usage: node karb.js n mode(0=exhaustive,1=random) trials seed
const n = +process.argv[2], mode = +process.argv[3], trials = +process.argv[4]; let seed = (+process.argv[5]) >>> 0 || 1;
const U = [], W = [];
for (let v = 1; v < n; v++) for (let u = 0; u < n; u++) if (u !== v) { U.push(u); W.push(v); }
const m = U.length, full = 1 << n;
// precompute for each Z (even mask, nonempty, root excluded) the list of entering arcs
const enter = [];
for (let Z = 2; Z < full; Z += 2) { const L = []; for (let a = 0; a < m; a++) if (((Z >> W[a]) & 1) && !((Z >> U[a]) & 1)) L.push(a); enter.push(L); }
function ok(x, need) { for (const L of enter) { let s = 0; for (const a of L) s += x[a]; if (s < need) return false; } return true; }
function rnd() { seed ^= seed << 13; seed >>>= 0; seed ^= seed >>> 17; seed ^= seed << 5; seed >>>= 0; return seed; }
const c = new Array(m).fill(0), x1 = new Array(m), x2 = new Array(m);
const total = 3 ** m, iters = mode === 0 ? total : trials; let r4 = 0, cex = 0;
for (let it = 0; it < iters; it++) {
  if (mode === 0) { let t = it; for (let a = 0; a < m; a++) { c[a] = t % 3; t = Math.floor(t / 3); } }
  else for (let a = 0; a < m; a++) c[a] = rnd() % 3;
  if (!ok(c, 4)) continue;
  r4++;
  const ones = [];
  for (let a = 0; a < m; a++) { x1[a] = x2[a] = c[a] === 2 ? 1 : 0; if (c[a] === 1) ones.push(a); }
  const no = ones.length, lim = no ? 2 ** (no - 1) : 1; let found = false;
  for (let S = 0; S < lim && !found; S++) {
    for (let j = 0; j < no; j++) { const side = j === 0 ? 0 : Math.floor(S / 2 ** (j - 1)) % 2; x1[ones[j]] = side === 0 ? 1 : 0; x2[ones[j]] = side; }
    if (ok(x1, 2) && ok(x2, 2)) found = true;
  }
  if (!found) { cex++; console.log('COUNTEREXAMPLE n=' + n + ' ' + c.map((v, a) => v ? U[a] + '->' + W[a] + ':' + v : '').filter(s => s).join(' ')); }
}
console.log(JSON.stringify({ done: true, n, mode, iters, rooted4: r4, counterexamples: cex }));
