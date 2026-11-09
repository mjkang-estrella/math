"""Check G against the source's lemmas (arXiv:1812.03382v3) as a consistency audit (own code)."""
import json, sys, itertools
sys.path.insert(0, sys.argv[1])
from ir_core import closed_nbhd, ir_graph, private_nbrs, irredundant
edges = [tuple(int(c) for c in s) for s in "03 04 06 07 13 15 16 17 18 24 25 27 28 36 38 46 47 48 57 58".split()]
E = {frozenset(e) for e in edges}
N = closed_nbhd(9, edges)
IR, sets, adj, _ = ir_graph(9, edges)
idx = {s: i for i, s in enumerate(sets)}
nb = {i: set() for i in range(len(sets))}
for i, j in adj: nb[i].add(j); nb[j].add(i)
def dist(a, b):
    seen = {a: 0}; fr = [a]
    while fr:
        nx = []
        for x in fr:
            for y in nb[x]:
                if y not in seen: seen[y] = seen[x] + 1; nx.append(y)
        fr = nx
    return seen.get(b)
out = {"per_IR_set": [], "flip_sets_all_IR": True, "Lem_Not_Path_instances": [], "C4_in_H": False}
for X in sets:
    pos = [v for v in X if any(frozenset((v, u)) in E for u in X if u != v)]
    epn = {v: sorted(private_nbrs(N, X, v) - {v}) for v in X}
    nedges = sum(1 for a, b in itertools.combinations(X, 2) if frozenset((a, b)) in E)
    out["per_IR_set"].append({"X": sorted(X), "edges_in_G[X]": nedges, "positive_degree": sorted(pos), "EPN": epn})
    # all flip-sets: choose Y subset of vertices with EPN that includes all positive-degree vertices
    withepn = [v for v in X if epn[v]]
    for r in range(len(withepn) + 1):
        for Y in itertools.combinations(withepn, r):
            if not set(pos) <= set(Y): continue
            for choice in itertools.product(*[epn[y] for y in Y]):
                Xp = (X - set(Y)) | set(choice)
                if len(Xp) != len(X) or not irredundant(N, Xp) or Xp not in idx:
                    out["flip_sets_all_IR"] = False
                if len(pos) == 3 and set(Y) == set(pos):
                    out["Lem_Not_Path_instances"].append({"X": sorted(X), "Xprime": sorted(Xp), "d_H": dist(idx[X], idx[Xp]) if Xp in idx else None})
# induced C4 in H?
for a, b, c, d in itertools.permutations(range(len(sets)), 4):
    if b in nb[a] and c in nb[b] and d in nb[c] and a in nb[d] and c not in nb[a] and d not in nb[b]:
        out["C4_in_H"] = True
out["Lem_Not_Path_any_d3"] = any(i["d_H"] == 3 for i in out["Lem_Not_Path_instances"])
out["Cor_C4_i_any_single_edge_IR_set"] = any(p["edges_in_G[X]"] == 1 for p in out["per_IR_set"])
out["Cor_C4_ii_indep_with_two_EPN"] = any(p["edges_in_G[X]"] == 0 and sum(1 for v in p["EPN"] if p["EPN"][v]) >= 2 for p in out["per_IR_set"])
out["diam_H"] = max(dist(i, j) for i in range(len(sets)) for j in range(len(sets)))
out["max_deg_H"] = max(len(nb[i]) for i in nb)
out["has_independent_IR_set"] = any(p["edges_in_G[X]"] == 0 for p in out["per_IR_set"])
print(json.dumps(out, indent=1, default=str))
