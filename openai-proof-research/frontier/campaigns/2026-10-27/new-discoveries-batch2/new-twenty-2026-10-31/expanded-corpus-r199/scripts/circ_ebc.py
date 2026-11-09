"""337062: exact edge betweenness of the seven circulant classes (Newman-Miranda-Florez-Narayan,
arXiv:1709.04773, final Conjecture).  Circulants are vertex-transitive and rotation maps each
step class onto itself, so the betweenness of a step-s edge equals the sum over step-s edges of
the Brandes dependency from source 0.  Exact Fractions.
usage: circ_ebc.py nmin nmax
"""
import sys, json
from fractions import Fraction
from collections import deque

CLASSES = {
 3: lambda n: (20 + 8 * (n - 1), (1, 2 * n + 2, 2 * n + 4)),
 4: lambda n: (32 + 8 * (n - 1), (1, 2 * n + 5, 2 * n + 7)),
 5: lambda n: (20 + 16 * (n - 1), (1, 4 * n, 8 * n + 1)),
 6: lambda n: (28 + 16 * (n - 1), (1, 4 * n + 4, 8 * n + 5)),
 7: lambda n: (32 + 8 * (n - 1), (1, 2 * n + 5, 4 * n + 11)),
 8: lambda n: (32 + 8 * (n - 1), (1, 2 * n + 7, 4 * n + 11)),
 9: lambda n: (49 + 14 * (n - 1), (1, 2 * n + 6, 4 * n + 9)),
}

def step_class(m, d, steps):
    d %= m
    for s in steps:
        if d == s % m or d == (-s) % m: return s % m if (s % m) <= m // 2 else (-s) % m
    raise ValueError

def analyse(m, steps):
    S = sorted({min(s % m, (-s) % m) for s in steps})
    nb = lambda u: {(u + s) % m for s in S} | {(u - s) % m for s in S}
    # Brandes from source 0
    dist = [-1] * m; sigma = [0] * m; dist[0] = 0; sigma[0] = 1; order = []; q = deque([0])
    while q:
        u = q.popleft(); order.append(u)
        for v in nb(u):
            if dist[v] < 0: dist[v] = dist[u] + 1; q.append(v)
            if dist[v] == dist[u] + 1: sigma[v] += sigma[u]
    delta = [Fraction(0)] * m; tot = {s: Fraction(0) for s in S}
    for w in reversed(order):
        for v in nb(w):
            if dist[v] == dist[w] - 1:
                c = Fraction(sigma[v], sigma[w]) * (1 + delta[w])
                delta[v] += c
                tot[min((w - v) % m, (v - w) % m)] += c
    connected = all(x >= 0 for x in dist)
    deg = len(nb(0))
    return dict(m=m, steps=list(steps), distinct_steps=S, degree=deg, connected=connected,
                class_ebc={str(s): str(tot[s]) for s in S}, uniform=len(set(tot.values())) == 1)

lo, hi = int(sys.argv[1]), int(sys.argv[2])
for c, f in CLASSES.items():
    for n in range(lo, hi + 1):
        m, st = f(n)
        r = analyse(m, st); r.update(cls=c, n=n)
        print(json.dumps(r), flush=True)
