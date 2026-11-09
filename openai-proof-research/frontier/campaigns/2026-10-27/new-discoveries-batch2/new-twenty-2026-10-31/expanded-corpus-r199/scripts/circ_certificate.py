"""Certificate data for G = C_32(1,7,9) (Class 4, n = 1 of arXiv:1709.04773 Conjecture 2.1).
Outputs: distance and shortest-path-count rows from vertex 0 (the graph is a Cayley graph of Z_32,
so d(x,y) = d(0,y-x), sigma_xy = sigma_{0,y-x}); the literal ordered-pair betweenness
B'(e) = sum_{x != y} sigma_xy(e)/sigma_xy for the edges {0,1}, {0,7}, {0,9}, computed directly over
all 32*31 ordered pairs with sigma_xy(uv) = sigma_xu*sigma_vy*[d(x,u)+1+d(v,y)=d(x,y)] + (u<->v).
usage: circ_certificate.py m s1 s2 ...
"""
import sys, json
from fractions import Fraction
from collections import deque
m = int(sys.argv[1]); S = [int(x) for x in sys.argv[2:]]
nb = lambda u: sorted({(u + s) % m for s in S} | {(u - s) % m for s in S})
d0 = [-1] * m; g0 = [0] * m; d0[0] = 0; g0[0] = 1; q = deque([0])
while q:
    u = q.popleft()
    for v in nb(u):
        if d0[v] < 0: d0[v] = d0[u] + 1; q.append(v)
        if d0[v] == d0[u] + 1: g0[v] += g0[u]
D = lambda x, y: d0[(y - x) % m]
SG = lambda x, y: g0[(y - x) % m]
def Bprime(u, v):
    tot = Fraction(0)
    for x in range(m):
        for y in range(m):
            if x == y: continue
            c = 0
            if D(x, u) + 1 + D(v, y) == D(x, y): c += SG(x, u) * SG(v, y)
            if D(x, v) + 1 + D(u, y) == D(x, y): c += SG(x, v) * SG(u, y)
            if c: tot += Fraction(c, SG(x, y))
    return tot
vals = {f'{{0,{s}}}': Bprime(0, s % m) for s in S}
layers = {}
for y in range(m): layers.setdefault(d0[y], []).append(y)
out = dict(m=m, steps=S, degree=len(nb(0)), diameter=max(d0),
           dist_from_0=d0, sigma_from_0=g0, layers={str(k): v for k, v in sorted(layers.items())},
           Bprime_ordered={k: str(v) for k, v in vals.items()},
           Bprime_float={k: float(v) for k, v in vals.items()},
           differences={f'{a}-{b}': str(vals[a] - vals[b]) for a in vals for b in vals if a < b},
           wiener_check=dict(sum_over_edges_of_Bprime_equals_sum_ordered_distances=None))
# sanity identity: sum_e B'(e) = sum_{x != y} d(x,y)  (each shortest path of length d has d edges)
classes = {}
for s in S:
    classes[s] = vals[f'{{0,{s}}}']
total_edges_B = sum(m * classes[s] for s in S)          # each step class has m edges (2s != m)
total_dist = m * sum(d0)
out['wiener_check'] = dict(sum_e_Bprime=str(total_edges_B), sum_ordered_distances=total_dist,
                           equal=(total_edges_B == total_dist))
print(json.dumps(out))
