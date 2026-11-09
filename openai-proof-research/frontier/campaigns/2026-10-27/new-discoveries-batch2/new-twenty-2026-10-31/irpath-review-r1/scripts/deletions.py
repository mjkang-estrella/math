"""IR-graphs of G - v for each v (augmentation screen against printed source targets)."""
import json, sys
sys.path.insert(0, sys.argv[1])
from ir_core import ir_graph
edges = [tuple(int(c) for c in s) for s in "03 04 06 07 13 15 16 17 18 24 25 27 28 36 38 46 47 48 57 58".split()]
out = {}
for x in range(9):
    keep = [v for v in range(9) if v != x]; rl = {v: i for i, v in enumerate(keep)}
    E = [(rl[a], rl[b]) for a, b in edges if x not in (a, b)]
    IR, sets, adj, _ = ir_graph(8, E)
    deg = [0] * len(sets)
    for i, j in adj: deg[i] += 1; deg[j] += 1
    out[x] = {"IR": IR, "n_IR_sets": len(sets), "n_IR_edges": len(adj), "deg_seq": sorted(deg, reverse=True)}
print(json.dumps(out, indent=1))
