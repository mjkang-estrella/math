// Test the "equally-spaced circle labelling" property for bipartite (multi)graphs: exists theta: E -> Z_D (D=lcm of
// degrees) such that at each vertex v the incident labels are distinct and pairwise congruent mod D/d(v)
// (i.e. form a full coset of the order-d(v) subgroup). Sufficient for MathDB 388092 for every c simultaneously.
// Usage: node circlelabel.js seed trials maxside maxmult budget
const [seed0, trials, maxside, maxmult, budget] = process.argv.slice(2).map(Number);
let s = seed0 >>> 0 || 1;
const rnd = () => { s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0; return s / 4294967296; };
const ri = (a, b) => a + Math.floor(rnd() * (b - a + 1));
const gcd = (a, b) => b ? gcd(b, a % b) : a;
function labelable(nv, E) {
  const deg = new Array(nv).fill(0); for (const [u, v] of E) { deg[u]++; deg[v]++; }
  let D = 1; for (const d of deg) if (d) D = D / gcd(D, d) * d;
  const inc = Array.from({ length: nv }, () => []); E.forEach(([u, v], i) => { inc[u].push(i); inc[v].push(i); });
  // order edges by BFS so constraints bind early
  const lab = new Array(E.length).fill(-1), used = Array.from({ length: nv }, () => new Set()), res = new Array(nv).fill(-1);
  const order = []; const seen = new Array(E.length).fill(false), vs = new Array(nv).fill(false);
  for (let r = 0; r < nv; r++) { if (vs[r]) continue; const q = [r]; vs[r] = true; while (q.length) { const x = q.shift(); for (const e of inc[x]) { if (!seen[e]) { seen[e] = true; order.push(e); } const y = E[e][0] === x ? E[e][1] : E[e][0]; if (!vs[y]) { vs[y] = true; q.push(y); } } } }
  let nodes = 0;
  function canPut(v, x) { const m = D / deg[v]; if (used[v].has(x)) return false; if (res[v] >= 0 && x % m !== res[v]) return false; return true; }
  function dfs(j) {
    if (++nodes > budget) throw 'budget';
    if (j === order.length) return true;
    const e = order[j], [u, v] = E[e];
    for (let x = 0; x < D; x++) {
      if (!canPut(u, x) || !canPut(v, x)) continue;
      const ru = res[u], rv = res[v];
      used[u].add(x); used[v].add(x); if (ru < 0) res[u] = x % (D / deg[u]); if (rv < 0) res[v] = x % (D / deg[v]);
      if (dfs(j + 1)) return true;
      used[u].delete(x); used[v].delete(x); res[u] = ru; res[v] = rv;
      if (j === 0) break; // global rotation symmetry
    }
    return false;
  }
  return dfs(0);
}
let fails = 0, to = 0, done = 0;
for (let t = 0; t < trials; t++) {
  const a = ri(1, maxside), b = ri(1, maxside), pr = 0.2 + 0.8 * rnd(), E = [];
  for (let i = 0; i < a; i++) for (let j = 0; j < b; j++) if (rnd() < pr) { const m = ri(1, maxmult); for (let r = 0; r < m; r++) E.push([i, a + j]); }
  if (!E.length) continue;
  try { if (!labelable(a + b, E)) { fails++; if (fails <= 5) console.log(JSON.stringify({ NOT_LABELABLE: true, a, b, E })); } done++; }
  catch (e) { if (e === 'budget') to++; else throw e; }
}
console.log(JSON.stringify({ finished: true, trials, done, fails, timeouts: to }));
