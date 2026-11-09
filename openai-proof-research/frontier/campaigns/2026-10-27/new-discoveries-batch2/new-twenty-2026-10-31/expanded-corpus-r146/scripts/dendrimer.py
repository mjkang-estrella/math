# 330508: Dehmer-Kraus Conjecture 4.2 (MATCH 68 (2012) 889-912), I_{f3} with f3(v) = c_{orbit(v)} * ecc(v),
# orbit(v) = distance from the centre.  Exact rational distributions, entropy in bits.
from fractions import Fraction as F
import math, json
def tree_info(n, edges):
    adj = {v: set() for v in range(n)}
    for a, b in edges: adj[a].add(b); adj[b].add(a)
    def bfs(s):
        d = {s: 0}; q = [s]
        for v in q:
            for u in adj[v]:
                if u not in d: d[u] = d[v] + 1; q.append(u)
        return d
    D = [bfs(v) for v in range(n)]
    ecc = [max(D[v].values()) for v in range(n)]
    r = min(ecc); centre = [v for v in range(n) if ecc[v] == r]
    orbit = [min(D[c][v] for c in centre) for v in range(n)]
    return ecc, orbit, r
def entropy(vals):
    s = sum(vals); return -sum(float(x / s) * math.log2(float(x / s)) for x in vals)
def I(n, edges, c):
    ecc, orbit, r = tree_info(n, edges)
    return entropy([c[orbit[v]] * ecc[v] for v in range(n)])
out = {}
for n in (5, 7, 9, 11):
    r = (n - 1) // 2
    path = [(i, i + 1) for i in range(n - 1)]; star = [(0, i) for i in range(1, n)]
    c_unif = [F(1, r + i) for i in range(r + 1)]          # nonincreasing; c_i (r+i) constant on the path
    out[f'n={n}'] = dict(weights=[str(x) for x in c_unif], I_path=I(n, path, c_unif), I_star=I(n, star, c_unif), log2n=math.log2(n),
                         const1_I_path=I(n, path, [1] * (r + 1)), const1_I_star=I(n, star, [1] * (r + 1)))
print(json.dumps(out, indent=1))
