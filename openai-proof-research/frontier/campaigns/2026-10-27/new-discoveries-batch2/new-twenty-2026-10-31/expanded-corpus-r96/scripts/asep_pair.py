"""Exact rank of the common tight system of vertex x and given tours (368807 diagnostics)."""
import sys, json, numpy as np
from fractions import Fraction
from math import lcm
sys.path.insert(0, __import__('os').path.dirname(__file__))
from asep import build, tours
from asep_verify import int_rank
n = int(sys.argv[1]); X = json.load(open(sys.argv[2]))['X']; idxs = [int(t) for t in sys.argv[3].split(',')]
arcs, Aeq, C, d, names = build(n); m = len(arcs)
xs = [Fraction(X[i][j]) for (i, j) in arcs]; D = lcm(*[v.denominator for v in xs]); xi = np.array([int(v * D) for v in xs])
Ci = C.astype(np.int64); di = d.astype(np.int64); I = (Ci @ xi - di * D) == 0
T = tours(n, arcs)
for t in idxs:
    Ti = T[t].astype(np.int64); J = I & ((Ci @ Ti - di) == 0)
    r = int_rank([list(map(int, row)) for row in np.vstack([Aeq.astype(np.int64), Ci[J]])])
    cyc = [0]; 
    succ = {a[0]: a[1] for k, a in enumerate(arcs) if Ti[k] == 1}
    while len(cyc) < n: cyc.append(succ[cyc[-1]])
    print(json.dumps({'tour_index': t, 'cycle': cyc, 'common_tight_inequalities': int(J.sum()), 'exact_rank': r, 'm': m, 'adjacent': r == m - 1, 'float_rank': int(np.linalg.matrix_rank(np.vstack([Aeq, C[J]])))}))
