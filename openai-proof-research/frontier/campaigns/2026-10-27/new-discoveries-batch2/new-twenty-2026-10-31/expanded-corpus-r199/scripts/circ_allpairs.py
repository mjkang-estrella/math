"""Independent all-pairs edge betweenness (no symmetry shortcut), exact Fractions.
EB(e) = sum over unordered pairs {s,t}, s != t, of sigma_st(e)/sigma_st, where for e = uv
sigma_st(e) = sigma_su*sigma_vt if d(s,u)+1+d(v,t) = d(s,t) (plus the symmetric orientation).
usage: circ_allpairs.py m s1 s2 [s3 ...]
"""
import sys, json
from fractions import Fraction
from collections import deque
m = int(sys.argv[1]); steps = [int(x) for x in sys.argv[2:]]
adj = [set() for _ in range(m)]
for u in range(m):
    for s in steps:
        adj[u].add((u + s) % m); adj[u].add((u - s) % m)
edges = sorted({(min(u, v), max(u, v)) for u in range(m) for v in adj[u]})
D = []; SG = []
for s in range(m):
    d = [-1] * m; g = [0] * m; d[s] = 0; g[s] = 1; q = deque([s])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if d[v] < 0: d[v] = d[u] + 1; q.append(v)
            if d[v] == d[u] + 1: g[v] += g[u]
    D.append(d); SG.append(g)
EB = {}
for (u, v) in edges:
    tot = Fraction(0)
    for s in range(m):
        for t in range(s + 1, m):
            c = 0
            if D[s][u] + 1 + D[v][t] == D[s][t]: c += SG[s][u] * SG[v][t]
            if D[s][v] + 1 + D[u][t] == D[s][t]: c += SG[s][v] * SG[u][t]
            if c: tot += Fraction(c, SG[s][t])
    EB[(u, v)] = tot
vals = sorted(set(EB.values()))
byclass = {}
for (u, v), x in EB.items():
    dd = min((v - u) % m, (u - v) % m); byclass.setdefault(dd, set()).add(x)
print(json.dumps(dict(m=m, steps=steps, edges=len(edges), connected=all(x >= 0 for x in D[0]),
                      distinct_values=[str(x) for x in vals], uniform=len(vals) == 1,
                      by_step={str(k): sorted(str(x) for x in v) for k, v in sorted(byclass.items())})))
