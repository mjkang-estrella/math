"""Survey all trees up to N vertices: Grundy values vs parity of the number of markable edges."""
import sys
import networkx as nx
import decomp
from collections import Counter

N = int(sys.argv[1])
for n in range(2, N + 1):
    cnt = Counter()
    bad = []
    for T in nx.nonisomorphic_trees(n):
        edges = list(T.edges())
        deg = dict(T.degree())
        m = sum(1 for (u, v) in edges if deg[u] > 1 and deg[v] > 1)
        g = decomp.grundy_original_tree(n, edges)
        cnt[g] += 1
        if (g == 0) != (m % 2 == 0):
            bad.append((m, g, sorted(d for d in deg.values()), edges))
    print("n =", n, "grundy distribution", dict(cnt), "counterexamples", len(bad), flush=True)
    for b in bad[:20]:
        print("   m=%d g=%d degseq=%s edges=%s" % b)
