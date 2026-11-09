# Cross-check csf() against brute-force Stanley subset expansion on all unicyclic graphs with n<=8, c in 3..6.
import sys, itertools
from collections import defaultdict
sys.argv = ['csf.py', '8', '3']
import os
__file__ = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'csf.py')
exec(open(__file__).read().split("if __name__")[0])
def brute(seq):
    c = len(seq); edges = [(j, (j + 1) % c) for j in range(c)]; nxt = [c]
    def expand(s, i, root):
        for (cs, ci) in trees[s][i]:
            v = nxt[0]; nxt[0] += 1; edges.append((root, v)); expand(cs, ci, v)
    for j, (a, i) in enumerate(seq): expand(a, i, j)
    n = nxt[0]; tot = defaultdict(int)
    for mask in range(1 << len(edges)):
        par = list(range(n))
        def f(x):
            while par[x] != x: par[x] = par[par[x]]; x = par[x]
            return x
        k = 0
        for t, (u, v) in enumerate(edges):
            if mask >> t & 1: k += 1; par[f(u)] = f(v)
        sz = defaultdict(int)
        for x in range(n): sz[f(x)] += 1
        tot[tuple(sorted(sz.values()))] += (-1) ** k
    return frozenset((p, v) for p, v in tot.items() if v)
cnt = 0
for n in range(3, 9):
    for c in range(3, n + 1):
        for comp in compositions(n, c):
            for choice in itertools.product(*[range(len(trees[a])) for a in comp]):
                seq = tuple(zip(comp, choice))
                if canon(seq) != seq: continue
                assert csf(seq) == brute(seq), seq; cnt += 1
print('csf matches brute force on', cnt, 'unicyclic graphs')
