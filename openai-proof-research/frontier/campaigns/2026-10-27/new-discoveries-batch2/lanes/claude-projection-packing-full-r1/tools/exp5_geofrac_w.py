"""Exp5: fractional geometric criterion (Theorem A') on the source's V=span(u,v) in R^5 (Prop 3.2).
Search pairs x, x' in V, ||x||=||x'||=1 peaking at distinct coordinates k != k', minimizing
max_j [(2|x_j|-1)_+ + (2|x'_j|-1)_+].  Value <= 1 means A' applies to this V (n=2 core).
The best float pair is then re-verified in exact rational arithmetic on a rationalized grid point."""
import json, math
from fractions import Fraction as Fr
u = [Fr(1), Fr(4, 5), Fr(1, 4), Fr(-1, 4), Fr(-4, 5)]
v = [Fr(0), Fr(3, 5), Fr(1), Fr(1), Fr(3, 5)]

def vec(a, b):
    x = [a * p + b * q for p, q in zip(u, v)]; m = max(abs(t) for t in x)
    return [t / m for t in x]

def pen(x, y):
    return max(max(0, 2 * abs(p) - 1) + max(0, 2 * abs(q) - 1) for p, q in zip(x, y))

M = 720; cands = []
for i in range(M):
    th = Fr(i, M)  # rational parameter on a rational "circle" a=1-2t style
    a, b = (1 - th, th) if th <= Fr(1, 2) else (1 - th, th)   # covers a,b>=0 directions
    for sgn in (1, -1):
        x = vec(a, sgn * b); k = max(range(5), key=lambda j: abs(x[j]))
        cands.append((x, k))
best = None
fl = [([float(t) for t in x], k) for x, k in cands]
for i in range(len(fl)):
    for j in range(i + 1, len(fl)):
        if fl[i][1] == fl[j][1]: continue
        p = pen(fl[i][0], fl[j][0])
        if best is None or p < best[0]: best = (p, i, j)
p, i, j = best
xe, ke = cands[i]; ye, kke = cands[j]
exact = pen(xe, ye)
print(json.dumps({'grid_points': len(cands), 'best_float_penalty': p, 'exact_penalty': str(exact),
                  'criterion_holds': exact <= 1, 'x': [str(t) for t in xe], 'peak_x': ke,
                  'y': [str(t) for t in ye], 'peak_y': kke}, indent=1))
