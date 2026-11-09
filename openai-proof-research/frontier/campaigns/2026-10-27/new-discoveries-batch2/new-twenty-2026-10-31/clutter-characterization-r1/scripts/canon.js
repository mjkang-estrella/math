// Exact canonical form of a 0/1 matrix under independent row and column permutations
// (colour-preserving bipartite graph isomorphism): refinement + individualization,
// minimum over the full search tree (no automorphism pruning => exact, slower).
'use strict';
function refine(A, rc, cc) {
  const n = A.length, m = A[0].length;
  for (;;) {
    const nr = A.map((row, i) => { const s = []; for (let j = 0; j < m; j++) if (row[j]) s.push(cc[j]); s.sort((a, b) => a - b); return rc[i] + ':' + s.join(','); });
    const nc = []; for (let j = 0; j < m; j++) { const s = []; for (let i = 0; i < n; i++) if (A[i][j]) s.push(rc[i]); s.sort((a, b) => a - b); nc.push(cc[j] + ':' + s.join(',')); }
    const ur = [...new Set(nr)].sort(), uc = [...new Set(nc)].sort();
    const rc2 = nr.map(x => ur.indexOf(x)), cc2 = nc.map(x => uc.indexOf(x));
    const same = new Set(rc2).size === new Set(rc).size && new Set(cc2).size === new Set(cc).size;
    rc = rc2; cc = cc2;
    if (same) return [rc, cc];
  }
}
function canon(A) {
  const n = A.length, m = A[0].length;
  let best = null;
  function rec(rc, cc) {
    [rc, cc] = refine(A, rc, cc);
    // first non-singleton cell (rows first, then cols)
    const cnt = (arr) => { const c = new Map(); arr.forEach(x => c.set(x, (c.get(x) || 0) + 1)); return c; };
    const crc = cnt(rc), ccc = cnt(cc);
    let cellR = [...crc.entries()].filter(e => e[1] > 1).map(e => e[0]).sort((a, b) => a - b)[0];
    if (cellR !== undefined) {
      for (let i = 0; i < n; i++) if (rc[i] === cellR) { const r2 = rc.map(x => 2 * x + 1); r2[i] = 2 * cellR; rec(r2, cc.slice()); }
      return;
    }
    let cellC = [...ccc.entries()].filter(e => e[1] > 1).map(e => e[0]).sort((a, b) => a - b)[0];
    if (cellC !== undefined) {
      for (let j = 0; j < m; j++) if (cc[j] === cellC) { const c2 = cc.map(x => 2 * x + 1); c2[j] = 2 * cellC; rec(rc.slice(), c2); }
      return;
    }
    const ri = [...Array(n).keys()].sort((a, b) => rc[a] - rc[b]), ci = [...Array(m).keys()].sort((a, b) => cc[a] - cc[b]);
    const s = ri.map(i => ci.map(j => A[i][j]).join('')).join('/');
    if (best === null || s < best) best = s;
  }
  rec(new Array(n).fill(0), new Array(m).fill(0));
  return best;
}
module.exports = { canon };
