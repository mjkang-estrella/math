"""Cross-check decomposition solver against brute force on all trees with <= N vertices."""
import sys
import networkx as nx
import brute
import decomp

N = int(sys.argv[1])
total = 0
for n in range(2, N + 1):
    for T in nx.nonisomorphic_trees(n):
        edges = list(T.edges())
        g1 = brute.grundy_tree(n, edges)
        g2 = decomp.grundy_original_tree(n, edges)
        total += 1
        if g1 != g2:
            print("MISMATCH", n, edges, g1, g2)
            sys.exit(1)
    print("n =", n, "ok", flush=True)
print("all", total, "trees agree")
