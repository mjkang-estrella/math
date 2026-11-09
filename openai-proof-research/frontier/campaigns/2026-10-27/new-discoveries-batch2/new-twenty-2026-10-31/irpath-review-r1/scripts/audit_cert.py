"""Entry-by-entry audit of certificate-350452.json against own closed-neighbourhood code."""
import json, sys
from itertools import combinations
sys.path.insert(0, sys.argv[1])
from ir_core import closed_nbhd, irredundant, private_nbrs
cert = json.load(open(sys.argv[2]))
stated = [tuple(int(c) for c in s) for s in "03 04 06 07 13 15 16 17 18 24 25 27 28 36 38 46 47 48 57 58".split()]
E = {frozenset(e) for e in stated}
assert {frozenset(e) for e in cert["edges"]} == E and len(cert["edges"]) == 20 and cert["num_edges"] == 20
assert cert["graph_vertices"] == list(range(9))
N = closed_nbhd(9, stated)
rep = {"errors": []}
def err(m): rep["errors"].append(m)
# four subsets: all 126, each witness v in D has N[v] subset N[D-v]
f = cert["four_subsets"]
seen = set()
for row in f:
    D = frozenset(row["set"]); v = row["vertex_without_private_neighbour"]
    if len(D) != 4: err(("4size", row))
    if D in seen: err(("4dup", row))
    seen.add(D)
    if v not in D: err(("4witness-not-in-D", row))
    if private_nbrs(N, D, v): err(("4witness-has-pn", row))
rep["four_rows"] = len(f); rep["four_distinct"] = len(seen)
rep["four_cover_all"] = seen == {frozenset(c) for c in combinations(range(9), 4)}
# three subsets
t = cert["three_subsets"]; seen3 = set(); irr3 = []
for row in t:
    D = frozenset(row["set"])
    if len(D) != 3 or D in seen3: err(("3bad", row))
    seen3.add(D)
    truth = irredundant(N, D)
    if row["irredundant"] != truth: err(("3flag", row, truth))
    if truth:
        irr3.append(D)
        pn = {int(k): set(v) for k, v in row["private_neighbours"].items()}
        for v in D:
            if pn.get(v) != private_nbrs(N, D, v): err(("3pn", row))
    else:
        v = row["vertex_without_private_neighbour"]
        if v not in D or private_nbrs(N, D, v): err(("3witness", row))
rep["three_rows"] = len(t); rep["three_cover_all"] = seen3 == {frozenset(c) for c in combinations(range(9), 3)}
rep["three_irredundant"] = sorted(sorted(D) for D in irr3)
rep["IR_sets_field_matches"] = {frozenset(s) for s in cert["IR_sets"]} == set(irr3) and len(cert["IR_sets"]) == 9
rep["IR_number_field"] = cert["IR_number"]
# pairs
pairs = cert["IR_set_pairs"]; seenp = set(); nadj = 0
for row in pairs:
    A = frozenset(row["A"]); B = frozenset(row["B"])
    key = frozenset((A, B))
    if A == B or key in seenp or A not in irr3 or B not in irr3: err(("pbad", row))
    seenp.add(key)
    truth = any(frozenset((u, v)) in E and B == (A - {u}) | {v} for u in A for v in B)
    if row["adjacent"] != truth: err(("padj", row, truth))
    if truth:
        nadj += 1
        u, v = row["swap"]
        if not (u in A and v in B and frozenset((u, v)) in E and B == (A - {u}) | {v}): err(("pswap", row))
    elif row["swap"] is not None: err(("pswap-nonnull", row))
rep["pair_rows"] = len(pairs); rep["pairs_cover_all"] = len(seenp) == 36; rep["adjacent_pairs"] = nadj
po = [frozenset(s) for s in cert["path_order"]]
rep["path_order_is_hamiltonian_path_of_adjacency"] = (set(po) == set(irr3) and len(po) == 9 and
    all(any(frozenset((u, v)) in E and po[k+1] == (po[k] - {u}) | {v} for u in po[k] for v in po[k+1]) for k in range(8)))
# heredity check: every subset of every irredundant set is irredundant (sanity for the proof step)
allirr = [frozenset(D) for k in range(10) for D in combinations(range(9), k) if irredundant(N, D)]
rep["heredity_holds_on_G"] = all(irredundant(N, frozenset(S)) for D in allirr for k in range(len(D)) for S in combinations(sorted(D), k))
rep["n_errors"] = len(rep["errors"])
print(json.dumps(rep, indent=1, default=str))
