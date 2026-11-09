"""Rebuild G from the textual description (K_{3,3,3} minus 05,08,14,23,26,37,56),
recompute everything and audit certificate-350452.json entry by entry (read as data)."""
import json, sys
from itertools import combinations
sys.path.insert(0, sys.argv[1])  # explicit lane scripts dir (not __file__)
from ir_core import closed_nbhd, irredundant, private_nbrs, ir_graph, classify
cert_path = sys.argv[2]
parts = [{0, 1, 2}, {3, 4, 5}, {6, 7, 8}]
part = {v: i for i, P in enumerate(parts) for v in P}
deleted = {frozenset(map(int, s)) for s in "05 08 14 23 26 37 56".split()}
for e in deleted:
    a, b = sorted(e); assert part[a] != part[b], e
edges = sorted(tuple(sorted((a, b))) for a, b in combinations(range(9), 2)
               if part[a] != part[b] and frozenset((a, b)) not in deleted)
out = {}
out["n_edges"] = len(edges)
out["edges"] = ["%d%d" % e for e in edges]
stated = "03 04 06 07 13 15 16 17 18 24 25 27 28 36 38 46 47 48 57 58".split()
out["edges_match_stated_list"] = out["edges"] == stated
N = closed_nbhd(9, edges)
out["closed_nbhds"] = {v: sorted(N[v]) for v in range(9)}
out["degrees"] = sorted(len(N[v]) - 1 for v in range(9))
IR, sets, adj, irr = ir_graph(9, edges)
out["IR"] = IR
out["count_irredundant_by_size"] = {k: sum(1 for D in irr if len(D) == k) for k in range(10)}
out["IR_sets"] = [sorted(s) for s in sets]
out["IR_graph_edges"] = [[sorted(sets[i]), sorted(sets[j])] for i, j in adj]
out["classify"] = classify(len(sets), adj)
# order the path and compare with the claimed path
claimed = [[0,1,2],[0,2,7],[0,4,7],[4,6,7],[6,7,8],[1,6,8],[1,3,8],[3,5,8],[3,4,5]]
cl = [frozenset(x) for x in claimed]
out["claimed_path_sets_equal_IR_sets"] = set(cl) == set(sets)
adjset = {frozenset((sets[i], sets[j])) for i, j in adj}
out["claimed_path_edges_equal_IR_graph_edges"] = adjset == {frozenset((cl[k], cl[k+1])) for k in range(8)}
out["private_nbrs_of_IR_sets"] = {str(sorted(s)): {v: sorted(private_nbrs(N, s, v)) for v in sorted(s)} for s in sets}
# automorphism group order
from itertools import permutations
E = {frozenset(e) for e in edges}
aut = 0
for p in permutations(range(9)):
    if all(frozenset((p[a], p[b])) in E for a, b in edges):
        aut += 1
out["aut_order"] = aut
# independence / domination flags of IR-sets
out["independent_IR_sets"] = [sorted(s) for s in sets if not any(frozenset(x) in E for x in combinations(s, 2))]
# ---- certificate audit ----
cert = json.load(open(cert_path))
out["cert_top_keys"] = sorted(cert.keys())
aud = {}
def as_set(x):
    if isinstance(x, str):
        return frozenset(int(c) for c in x if c.isdigit())
    return frozenset(int(c) for c in x)
for key in ("four_subsets", "three_subsets", "IR_set_pairs"):
    aud[key] = {"present": key in cert}
four = cert.get("four_subsets")
aud["four_subsets"]["type"] = type(four).__name__
aud["four_subsets"]["sample"] = (four[:2] if isinstance(four, list) else list(four.items())[:2]) if four else None
out["cert_audit_raw"] = aud
# also record cert graph if present
for k in ("edges", "graph", "G", "vertices", "edge_list"):
    if k in cert:
        out["cert_" + k] = cert[k]
print(json.dumps(out, indent=1, default=str))
