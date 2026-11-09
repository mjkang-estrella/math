// MathDB 388092 counterexample search (Correa-Goemans proportional factors). c_i = p_i/N with integer p_i, so
// floor/ceil of c_i d are exact integer ops. DFS over edges with per-vertex need/room pruning and a node budget.
// Usage: node propfactor.js seed trials maxside maxmult maxN budget
const [seed0, trials, maxside, maxmult, maxN, budget] = process.argv.slice(2).map(Number);
let s = seed0 >>> 0 || 1;
const rnd = () => { s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0; return s / 4294967296; };
const ri = (a, b) => a + Math.floor(rnd() * (b - a + 1));
function solve(nv, E, p, N) {
  const k = p.length, deg = new Array(nv).fill(0);
  for (const [u, v] of E) { deg[u]++; deg[v]++; }
  const lo = [], hi = [];
  for (let v = 0; v < nv; v++) { lo.push(p.map(x => Math.floor(x * deg[v] / N))); hi.push(p.map(x => Math.ceil(x * deg[v] / N))); }
  const cnt = Array.from({ length: nv }, () => new Array(k).fill(0)), rem = deg.slice();
  const ord = E.map((e, i) => i).sort((a, b) => (deg[E[b][0]] + deg[E[b][1]]) - (deg[E[a][0]] + deg[E[a][1]]));
  let nodes = 0;
  const ok = v => { let need = 0, room = 0; for (let i = 0; i < k; i++) { need += Math.max(0, lo[v][i] - cnt[v][i]); room += hi[v][i] - cnt[v][i]; } return need <= rem[v] && rem[v] <= room; };
  for (let v = 0; v < nv; v++) if (!ok(v)) return false;
  function dfs(j) {
    if (++nodes > budget) throw 'budget';
    if (j === ord.length) return true;
    const [u, v] = E[ord[j]]; rem[u]--; rem[v]--;
    for (let i = 0; i < k; i++) {
      if (cnt[u][i] < hi[u][i] && cnt[v][i] < hi[v][i]) {
        cnt[u][i]++; cnt[v][i]++;
        if (ok(u) && ok(v) && dfs(j + 1)) return true;
        cnt[u][i]--; cnt[v][i]--;
      }
    }
    rem[u]++; rem[v]++; return false;
  }
  return dfs(0);
}
let timeouts = 0, done = 0;
for (let t = 0; t < trials; t++) {
  const k = [3, 3, 3, 4, 5][ri(0, 4)], a = ri(2, maxside), b = ri(2, maxside), pr = 0.25 + 0.75 * rnd(), E = [];
  for (let i = 0; i < a; i++) for (let j = 0; j < b; j++) if (rnd() < pr) { const m = ri(1, maxmult); for (let r = 0; r < m; r++) E.push([i, a + j]); }
  if (!E.length) continue;
  const N = ri(k + 1, maxN); const cuts = new Set(); while (cuts.size < k - 1) cuts.add(ri(1, N - 1));
  const cs = [...cuts].sort((x, y) => x - y), p = []; let prev = 0; for (const x of cs.concat([N])) { p.push(x - prev); prev = x; }
  try { if (!solve(a + b, E, p, N)) console.log(JSON.stringify({ COUNTEREXAMPLE: true, a, b, E, p, N })); done++; }
  catch (e) { if (e === 'budget') { timeouts++; console.log(JSON.stringify({ TIMEOUT: true, a, b, E, p, N })); } else throw e; }
}
console.log(JSON.stringify({ finished: true, seed: seed0, trials, decided: done, timeouts, maxside, maxmult, maxN }));
