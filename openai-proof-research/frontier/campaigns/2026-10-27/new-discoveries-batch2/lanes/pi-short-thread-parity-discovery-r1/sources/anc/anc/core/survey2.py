"""For each n: Grundy distribution over all trees, number of parity counterexamples, max Grundy tree."""
import sys, pickle
import networkx as nx
import decomp
from collections import Counter
n = int(sys.argv[1])
cnt = Counter(); nbad = 0; best = (-1, None); bad_examples=[]
for T in nx.nonisomorphic_trees(n):
    edges = list(T.edges())
    deg = dict(T.degree())
    m = sum(1 for (u, v) in edges if deg[u] > 1 and deg[v] > 1)
    g = decomp.grundy_original_tree(n, edges)
    cnt[g] += 1
    if (g == 0) != (m % 2 == 0):
        nbad += 1
        if len(bad_examples)<200: bad_examples.append((m,g,edges))
    if g > best[0]:
        best = (g, edges)
print("n=%d trees=%d dist=%s counterexamples=%d max=%d maxtree=%s" % (n, sum(cnt.values()), dict(sorted(cnt.items())), nbad, best[0], best[1]), flush=True)
pickle.dump((cnt,nbad,best,bad_examples), open("survey_n%d.pkl"%n,"wb"))
