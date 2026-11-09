# Exact re-decision of DFS-budget TIMEOUT instances for MathDB 388092 using HiGHS MILP (scipy.optimize.milp).
# Feasibility of x_{e,i} in {0,1}: sum_i x_{e,i}=1; floor(p_i d/N) <= sum_{e at v} x_{e,i} <= ceil(p_i d/N).
import sys, json
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
def decide(a, b, E, p, N):
    nv = a + b; k = len(p); m = len(E); deg = [0] * nv
    for u, v in E: deg[u] += 1; deg[v] += 1
    nvar = m * k; rows = m + nv * k
    A = lil_matrix((rows, nvar)); lo = np.zeros(rows); hi = np.zeros(rows)
    for e in range(m):
        for i in range(k): A[e, e * k + i] = 1
        lo[e] = hi[e] = 1
    for e, (u, v) in enumerate(E):
        for i in range(k):
            A[m + u * k + i, e * k + i] = 1; A[m + v * k + i, e * k + i] = 1
    for v in range(nv):
        for i in range(k):
            r = m + v * k + i; lo[r] = (p[i] * deg[v]) // N; hi[r] = -((-p[i] * deg[v]) // N)
    res = milp(np.zeros(nvar), constraints=LinearConstraint(A.tocsr(), lo, hi), integrality=np.ones(nvar), bounds=Bounds(0, 1), options={'time_limit': 120})
    if res.status == 0:
        x = np.round(res.x).astype(int).reshape(m, k)
        # independent exact verification of the returned partition
        assert all(x[e].sum() == 1 for e in range(m))
        cnt = [[0] * k for _ in range(nv)]
        for e, (u, v) in enumerate(E):
            i = int(np.argmax(x[e])); cnt[u][i] += 1; cnt[v][i] += 1
        for v in range(nv):
            for i in range(k):
                assert (p[i] * deg[v]) // N <= cnt[v][i] <= -((-p[i] * deg[v]) // N)
        return 'feasible-verified'
    return {2: 'INFEASIBLE', 1: 'time-limit'}.get(res.status, 'status%d' % res.status)
if __name__ == "__main__":
  out = {}
  for line in open(sys.argv[1]):
      line = line.strip()
      if not line.startswith('{"TIMEOUT"'): continue
      d = json.loads(line)
      r = decide(d['a'], d['b'], d['E'], d['p'], d['N'])
      out[r] = out.get(r, 0) + 1
      if r != 'feasible-verified': print(json.dumps({'result': r, **d}))
  print(json.dumps(out))
