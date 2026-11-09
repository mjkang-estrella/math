"""Print all 3-colourings (bouquet colour-count vectors) of a 3-vertex multigraph under the Delta_even<=2 reading.
usage: sedge_show.py m01 m02 m12"""
import sys, itertools
m = list(map(int, sys.argv[1:4])); pairs = [(0,1),(0,2),(1,2)]
ok = lambda d: d == 0 or d == 2 or d % 2 == 1
comps = lambda k: [(a, b, k-a-b) for a in range(k+1) for b in range(k+1-a)]
sols = []
for cs in itertools.product(*(comps(k) for k in m)):
    deg = [[0]*3 for _ in range(3)]
    for (u, v), c in zip(pairs, cs):
        for j in range(3): deg[u][j] += c[j]; deg[v][j] += c[j]
    if all(ok(deg[w][j]) for w in range(3) for j in range(3)): sols.append((cs, deg))
print(len(sols)); [print(s) for s in sols[:6]]
