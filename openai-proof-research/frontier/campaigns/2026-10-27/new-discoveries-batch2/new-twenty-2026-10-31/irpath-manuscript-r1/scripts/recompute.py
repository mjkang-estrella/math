"""Fresh recomputation of every finite fact about the 9-vertex graph G printed in the manuscript.

Written in this lane from the source definitions (arXiv:1812.03382v3, Sec. 1.1-1.2); it imports
no other lane's code. Standard library only.

Usage: python3 -I scripts/recompute.py OUT.json   (OUT opened with mode 'x')
"""
import sys
sys.dont_write_bytecode = True
import itertools, json, hashlib

V = list(range(9))
PARTS = [(0, 1, 2), (3, 4, 5), (6, 7, 8)]
DELETED = ["05", "08", "14", "23", "26", "37", "56"]
STATED_EDGES = "03 04 06 07 13 15 16 17 18 24 25 27 28 36 38 46 47 48 57 58".split()
WALK = [(0, 1, 2), (0, 2, 7), (0, 4, 7), (4, 6, 7), (6, 7, 8), (1, 6, 8), (1, 3, 8), (3, 5, 8), (3, 4, 5)]


def part(v):
    return v // 3


def fs(s):
    return "".join(str(x) for x in sorted(s))


# ---- the graph -------------------------------------------------------------------------
E = set()
for a, b in itertools.combinations(V, 2):
    if part(a) != part(b):
        E.add(frozenset((a, b)))
for e in DELETED:
    E.remove(frozenset((int(e[0]), int(e[1]))))
assert sorted(fs(e) for e in E) == sorted(STATED_EDGES), "edge list mismatch"
adj = {v: {u for u in V if frozenset((u, v)) in E} for v in V}
N = {v: adj[v] | {v} for v in V}                          # closed neighbourhoods
Nbar = {v: set(V) - N[v] for v in V}                     # neighbourhoods in the complement


def Nset(D):
    out = set()
    for u in D:
        out |= N[u]
    return out


def PN(v, D):
    """Source definition: PN(v,D) = N[v] - N[D - {v}]."""
    return N[v] - Nset(set(D) - {v})


def irredundant(D):
    return all(PN(v, D) for v in D)


def CN(S):
    """common complement neighbourhood of a nonempty set S"""
    S = list(S)
    out = set(Nbar[S[0]])
    for u in S[1:]:
        out &= Nbar[u]
    return out


facts = {}
facts["edges"] = sorted(fs(e) for e in E)
facts["n_edges"] = len(E)
facts["degrees"] = {v: len(adj[v]) for v in V}
facts["closed_nbhd"] = {v: sorted(N[v]) for v in V}
facts["complement_nbhd"] = {v: sorted(Nbar[v]) for v in V}
# the seven deleted edges: a path 8-0-5-6-2-3-7 plus the edge 1-4
dp = [8, 0, 5, 6, 2, 3, 7]
assert {frozenset((dp[i], dp[i + 1])) for i in range(6)} | {frozenset((1, 4))} == \
    {frozenset((int(e[0]), int(e[1]))) for e in DELETED}
facts["deleted_edges_structure"] = "path 8-0-5-6-2-3-7 plus edge 1-4"
# connectivity
seen, st = {0}, [0]
while st:
    x = st.pop()
    for y in adj[x]:
        if y not in seen:
            seen.add(y); st.append(y)
facts["G_connected"] = len(seen) == 9
# automorphism group by brute force over 9! permutations
aut = 0
Elist = [tuple(e) for e in E]
for p in itertools.permutations(V):
    if all(frozenset((p[a], p[b])) in E for a, b in Elist):
        aut += 1
facts["automorphism_group_order"] = aut

# ---- lemma: PN(v,D) = CN(D-v) minus Nbar(v), checked on all subsets ---------------------
lemma_checks = 0
for k in range(2, 10):
    for D in itertools.combinations(V, k):
        for v in D:
            assert PN(v, D) == CN(set(D) - {v}) - Nbar[v]
            lemma_checks += 1
facts["lemma_PN_formula_checks"] = lemma_checks

# ---- irredundant sets of every size (brute force over all 512 subsets) ------------------
by_size = [0] * 10
irr_all = []
for k in range(10):
    for D in itertools.combinations(V, k):
        if irredundant(D):
            by_size[k] += 1
            irr_all.append(frozenset(D))
facts["irredundant_counts_by_size"] = by_size
IR = max(len(D) for D in irr_all)
facts["IR"] = IR
irr_set = set(irr_all)
# heredity on G
for D in irr_all:
    for v in D:
        assert D - {v} in irr_set
facts["heredity_checked_on_irredundant_sets"] = len(irr_all)

# ---- pairs: common complement neighbourhoods --------------------------------------------
pair_cn = {fs(p): sorted(CN(p)) for p in itertools.combinations(V, 2)}
facts["pair_common_complement_nbhd"] = pair_cn
facts["pairs_with_empty_CN"] = sorted(k for k, c in pair_cn.items() if not c)

# ---- triples: good = nonempty common complement neighbourhood ---------------------------
triple_cn = {fs(t): sorted(CN(t)) for t in itertools.combinations(V, 3)}
good_triples = sorted(k for k, c in triple_cn.items() if c)
facts["good_triples"] = {k: triple_cn[k] for k in good_triples}
facts["n_good_triples"] = len(good_triples)

# ---- four-subsets -------------------------------------------------------------------------
four = []
n_bad_triple = 0
all_good_4 = []
for D in itertools.combinations(V, 4):
    Ds = set(D)
    failing = [v for v in D if not PN(v, D)]
    assert failing, ("irredundant 4-set!", D)
    bad = [v for v in D if not CN(Ds - {v})]      # D-v is a bad triple => v has PN empty
    for v in bad:
        assert not PN(v, D)
    if bad:
        n_bad_triple += 1
        four.append({"D": fs(D), "witness": bad[0], "reason": "bad triple " + fs(Ds - {bad[0]})})
    else:
        w = failing[0]
        all_good_4.append({"D": fs(D), "witness": w,
                           "CN(D-w)": sorted(CN(Ds - {w})), "Nbar(w)": sorted(Nbar[w])})
        four.append({"D": fs(D), "witness": w, "reason": "CN(D-w) subset of Nbar(w)"})
facts["n_four_subsets"] = len(four)
facts["four_with_bad_triple"] = n_bad_triple
facts["four_all_triples_good"] = all_good_4
facts["four_subsets"] = four

# ---- three-subsets ------------------------------------------------------------------------
three = []
fail_a, fail_b = [], []
irr3 = []
for D in itertools.combinations(V, 3):
    Ds = set(D)
    pns = {v: sorted(PN(v, D)) for v in D}
    if all(pns.values()):
        irr3.append(fs(D))
        three.append({"D": fs(D), "irredundant": True, "PN": pns,
                      "independent": not any(frozenset(p) in E for p in itertools.combinations(D, 2))})
        continue
    emptyCN = [v for v in D if not CN(Ds - {v})]
    if emptyCN:
        v = emptyCN[0]
        fail_a.append(fs(D))
        three.append({"D": fs(D), "irredundant": False, "witness": v,
                      "reason": "pair %s has empty CN" % fs(Ds - {v})})
    else:
        v = [u for u in D if not pns[u]][0]
        fail_b.append({"D": fs(D), "witness": v, "CN(D-v)": sorted(CN(Ds - {v})), "Nbar(v)": sorted(Nbar[v])})
        three.append({"D": fs(D), "irredundant": False, "witness": v,
                      "reason": "CN(D-v) nonempty and inside Nbar(v)"})
facts["n_three_subsets"] = len(three)
facts["irredundant_three_sets"] = irr3

# ---- the organisation used in the manuscript ----------------------------------------------
# U(S) = V - N[S] (vertices not dominated by S); PN(v,D) = U(D-v) - U(D) for |D| >= 2.
def U(S):
    return set(V) - Nset(S)


for k in range(2, 10):
    for D in itertools.combinations(V, k):
        for v in D:
            assert PN(v, D) == U(set(D) - {v}) - U(D)
        assert U(D) == CN(D)
empty_pairs = sorted(fs(p) for p in itertools.combinations(V, 2) if not U(p))
facts["empty_pairs"] = {p: ("G-edge" if frozenset((int(p[0]), int(p[1]))) in E else "deleted edge")
                        for p in empty_pairs}
cls_a, cls_b, cls_c = [], [], []
for T in itertools.combinations(V, 3):
    Ts = set(T)
    has_empty = any(fs(p) in empty_pairs for p in itertools.combinations(T, 2))
    if has_empty:
        cls_a.append(fs(T)); assert not irredundant(T)
    elif U(T):
        wit = [v for v in T if U(Ts - {v}) == U(T)]
        assert wit and not irredundant(T)
        cls_b.append({"T": fs(T), "U(T)": sorted(U(T)), "witness": wit[0],
                      "U(T-witness)": sorted(U(Ts - {wit[0]}))})
    else:
        assert irredundant(T)
        for v in T:
            assert PN(v, T) == U(Ts - {v})
        cls_c.append(fs(T))
facts["triples_class_a_contain_empty_pair"] = cls_a
facts["triples_class_b_nondominating"] = cls_b
facts["triples_class_c_dominating_no_empty_pair"] = cls_c
assert sorted(cls_c) == sorted(irr3)
assert sorted(d["T"] for d in cls_b) == good_triples
# 4-sets: those containing a dominating triple, and the rest
four_dom, four_rest = 0, []
for D in itertools.combinations(V, 4):
    Ds = set(D)
    dom = [v for v in D if not U(Ds - {v})]
    if dom:
        four_dom += 1
    else:
        w = [x for x in V if Nbar[x] == Ds]
        wit = [v for v in D if U(Ds - {v}) == U(D)]
        four_rest.append({"D": fs(D), "equals_Nbar_of": w, "U(D)": sorted(U(D)), "witness": wit[0],
                          "U(D-witness)": sorted(U(Ds - {wit[0]}))})
facts["four_containing_dominating_triple"] = four_dom
facts["four_without_dominating_triple"] = four_rest
# two IR-sets sharing two vertices: the 'share-two' graph on the nine sets is the path itself,
# so no three IR-sets pairwise share two vertices (heredity argument for IR(G) <= 3)
share2 = sorted((i, j) for i, j in itertools.combinations(range(9), 2)
                if len(set(WALK[i]) & set(WALK[j])) == 2)
assert share2 == [(i, i + 1) for i in range(8)]
assert not any(len(set(WALK[a]) & set(WALK[b])) == 2 and len(set(WALK[a]) & set(WALK[c])) == 2 and
               len(set(WALK[b]) & set(WALK[c])) == 2 for a, b, c in itertools.combinations(range(9), 3))
facts["share_two_pairs"] = share2
facts["three_fail_empty_pair_CN"] = fail_a
facts["three_fail_CN_inside_Nbar"] = fail_b
facts["three_subsets"] = three

# ---- IR-sets and IR-graph -------------------------------------------------------------------
irsets = sorted((D for D in irr_all if len(D) == IR), key=lambda s: sorted(s))
facts["n_IR_sets"] = len(irsets)
assert sorted(fs(D) for D in irsets) == sorted(fs(W) for W in WALK)
facts["IR_sets_path_order"] = [
    {"D": fs(W), "PN": {v: sorted(PN(v, W)) for v in W},
     "independent": not any(frozenset(p) in E for p in itertools.combinations(W, 2))}
    for W in WALK]


def swap(A, B):
    """source adjacency: exists u in A, v in B, uv in E, B = (A - {u}) | {v}"""
    for u in A:
        for v in B:
            if frozenset((u, v)) in E and set(B) == (set(A) - {u}) | {v}:
                return (u, v)
    return None


pairs = []
H_edges = []
n_share2 = 0
share2_nonadjacent = []
for i, j in itertools.combinations(range(9), 2):
    A, B = set(WALK[i]), set(WALK[j])
    s1, s2 = swap(A, B), swap(B, A)
    assert (s1 is None) == (s2 is None)             # symmetry of the source relation
    inter = len(A & B)
    rec = {"i": i, "j": j, "A": fs(A), "B": fs(B), "common": inter, "adjacent": s1 is not None}
    if inter == 2:
        n_share2 += 1
        u, = A - B; v, = B - A
        rec["out"], rec["in"], rec["uv_edge"] = u, v, frozenset((u, v)) in E
        if s1 is None:
            share2_nonadjacent.append({"A": fs(A), "B": fs(B), "out": u, "in": v})
    if s1 is not None:
        H_edges.append((i, j)); rec["swap"] = s1
    pairs.append(rec)
for A in irsets:
    assert swap(A, A) is None
facts["n_IR_set_pairs"] = len(pairs)
facts["n_pairs_sharing_two"] = n_share2
facts["pairs_sharing_two_nonadjacent"] = share2_nonadjacent
facts["IR_set_pairs"] = pairs
facts["IR_graph_edges"] = H_edges
facts["n_IR_graph_edges"] = len(H_edges)
facts["IR_graph_is_path_in_walk_order"] = sorted(H_edges) == [(i, i + 1) for i in range(8)]
facts["swaps_along_path"] = [{"from": fs(WALK[i]), "to": fs(WALK[i + 1]),
                              "out": swap(set(WALK[i]), set(WALK[i + 1]))[0],
                              "in": swap(set(WALK[i]), set(WALK[i + 1]))[1]} for i in range(8)]
deg = [sum(1 for e in H_edges if i in e) for i in range(9)]
facts["IR_graph_degrees_walk_order"] = deg
facts["IR_graph_max_degree"] = max(deg)
facts["independent_IR_sets"] = [fs(W) for W in WALK
                                if not any(frozenset(p) in E for p in itertools.combinations(W, 2))]

# ---- control: K_2 = P_2 -----------------------------------------------------------------------
NK = {0: {0, 1}, 1: {0, 1}}
irrK = [D for k in range(3) for D in itertools.combinations((0, 1), k)
        if all(NK[v] - set().union(*[NK[u] for u in D if u != v]) for v in D)]
IRK = max(len(D) for D in irrK)
facts["control_K2"] = {"IR": IRK, "IR_sets": [list(D) for D in irrK if len(D) == IRK],
                       "IR_graph": "K2 (the two singletons are swap-adjacent along edge 01)"}

summary = {k: facts[k] for k in ["n_edges", "degrees", "G_connected", "automorphism_group_order",
                                  "irredundant_counts_by_size", "IR", "n_IR_sets", "n_good_triples",
                                  "four_with_bad_triple", "n_three_subsets", "n_IR_set_pairs",
                                  "n_pairs_sharing_two", "n_IR_graph_edges", "IR_graph_is_path_in_walk_order",
                                  "IR_graph_max_degree", "independent_IR_sets", "lemma_PN_formula_checks"]}
summary["four_all_triples_good"] = [d["D"] for d in all_good_4]
summary["three_fail_empty_pair_CN"] = len(fail_a)
summary["three_fail_CN_inside_Nbar"] = len(fail_b)
summary["pairs_with_empty_CN"] = facts["pairs_with_empty_CN"]
summary["empty_pairs"] = facts["empty_pairs"]
summary["triple_classes_abc"] = [len(cls_a), len(cls_b), len(cls_c)]
summary["four_containing_dominating_triple"] = four_dom
summary["four_without_dominating_triple"] = [(d["D"], d["equals_Nbar_of"], d["witness"]) for d in four_rest]
summary["deleted_edges_structure"] = facts["deleted_edges_structure"]
facts["summary"] = summary
blob = json.dumps(facts, indent=1, sort_keys=True, default=list)
with open(sys.argv[1], "x") as f:
    f.write(blob)
print(json.dumps(summary, default=list))
print("sha256", hashlib.sha256(blob.encode()).hexdigest())
