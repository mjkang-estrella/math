"""368807: exact adjacency of vertex x to every tour in a slice, by exact integer rank of the common tight system.
x adjacent to tour T  iff  rank_Q [Aeq; C_{I(x) cap I(T)}] = m - 1.   usage: asep_exact_all.py n vertex.json lo hi"""
import sys, json, resource, numpy as np
from fractions import Fraction
from math import lcm
resource.setrlimit(resource.RLIMIT_CPU, (118, 118))
sys.path.insert(0, __import__('os').path.dirname(__file__))
from asep import build, tours
from asep_verify import int_rank
n = int(sys.argv[1]); X = json.load(open(sys.argv[2]))['X']; lo, hi = int(sys.argv[3]), int(sys.argv[4])
arcs, Aeq, C, d, names = build(n); m = len(arcs)
xs = [Fraction(X[i][j]) for (i, j) in arcs]; D = lcm(*[v.denominator for v in xs]); xi = np.array([int(v * D) for v in xs])
Ci = C.astype(np.int64); di = d.astype(np.int64); Ai = Aeq.astype(np.int64)
assert np.all(Ai @ xi == D) and np.all(Ci @ xi - di * D >= 0)
I = (Ci @ xi - di * D) == 0
vr = int_rank([list(map(int, r)) for r in np.vstack([Ai, Ci[I]])])
T = tours(n, arcs); hist = {}; adj = []
for t in range(lo, min(hi, len(T))):
    Ti = T[t].astype(np.int64); J = I & ((Ci @ Ti - di) == 0)
    r = int_rank([list(map(int, row)) for row in np.vstack([Ai, Ci[J]])])
    hist[r] = hist.get(r, 0) + 1
    if r == m - 1: adj.append(t)
print(json.dumps({'n': n, 'slice': [lo, hi], 'vertex_rank': vr, 'm': m, 'rank_histogram': {str(k): v for k, v in sorted(hist.items())}, 'adjacent_tours': adj}))
