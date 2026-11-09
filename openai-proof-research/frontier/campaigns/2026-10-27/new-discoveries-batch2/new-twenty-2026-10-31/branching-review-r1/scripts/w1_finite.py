"""Finite facts about W1 used by the D_m refutation, plus controls (review lane, independent code).

W1 on p1..p4 = 0..3: arcs 01,12,23,30 (Hamiltonian cycle), 02 (chord), 13,31 (2-cycle),
taken from the source's proof of Theorem 19(c): H = p1p2p3p4p1 and A(D') = {p2p4, p4p2, p1p3}.

Checks:
 (1) W1 basics: semicomplete, in-degrees, lambda(W1) and every root lacks a non-separating
     out-branching (source Theorem 19(b)).
 (2) Control digraphs: S4 (source: non-separating branching from every vertex, Figure 4) and the
     complete digraph on 4 vertices (Corollary 20).
 (3) The finite lemma over ALL 128 subsets T of A(W1):
     case e=p1,e'=p3: [p1 reaches all of B in T] => NOT([p3 reaches all in W1-T] and [all reach p3 in W1-T])
     case e=p3,e'=p1: [p3 reaches all of B in T] => NOT([p1 reaches all in W1-T] and [all reach p3 in W1-T])
     and which single conjunct already suffices (to size the Lean decide).
 (4) The m-independent cut table for lambda(D_m) >= 2: for nonempty Y subset of B,
     d^-_{W1}(Y) + #{entries with head in Y} >= 2   (the case A subset of X, Y = B \\ X)
     d^+_{W1}(X) + 2*[p3 in X] >= 2                 (the case X subset of B)
"""
import itertools, json

W1 = [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2), (1, 3), (3, 1)]
S4 = [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2), (2, 0), (1, 3), (3, 1)]
K4 = [(i, j) for i in range(4) for j in range(4) if i != j]


def reach_from(s, arcs, n=4):
    seen = {s}
    st = [s]
    while st:
        u = st.pop()
        for (a, b) in arcs:
            if a == u and b not in seen:
                seen.add(b); st.append(b)
    return seen


def reach_to(t, arcs, n=4):
    return reach_from(t, [(b, a) for (a, b) in arcs], n)


def strong(arcs, n=4):
    return len(reach_from(0, arcs, n)) == n and len(reach_to(0, arcs, n)) == n


def out_branchings(arcs, s, n=4):
    """all arc sets F: each v != s has exactly one in-arc in F, s has none, all reachable from s"""
    others = [v for v in range(n) if v != s]
    choices = [[(u, v) for (u, w) in arcs if w == v] for v in others]
    for pick in itertools.product(*choices):
        if len(reach_from(s, list(pick), n)) == n:
            yield list(pick)


def nonsep_roots(arcs, n=4):
    res = {}
    for s in range(n):
        res[s] = any(strong([a for a in arcs if a not in F], n) for F in out_branchings(arcs, s, n))
    return res


def lam(arcs, n=4):
    best = None
    for k in range(1, n):
        for X in itertools.combinations(range(n), k):
            X = set(X)
            c = sum(1 for (u, v) in arcs if u in X and v not in X)
            best = c if best is None else min(best, c)
    return best


out = {}
indeg = [sum(1 for (u, v) in W1 if v == x) for x in range(4)]
outdeg = [sum(1 for (u, v) in W1 if u == x) for x in range(4)]
semi = all(((i, j) in W1) or ((j, i) in W1) for i in range(4) for j in range(i + 1, 4))
out["W1"] = {"arcs": W1, "semicomplete": semi, "indeg": indeg, "outdeg": outdeg, "strong": strong(W1),
             "lambda": lam(W1), "nonsep_root": nonsep_roots(W1),
             "num_outbranchings_by_root": {s: len(list(out_branchings(W1, s))) for s in range(4)}}
out["S4_control"] = {"lambda": lam(S4), "nonsep_root": nonsep_roots(S4)}
out["K4_control"] = {"lambda": lam(K4), "nonsep_root": nonsep_roots(K4)}

# (3) finite lemma over all subsets
viol = {"case_p1": [], "case_p3": []}
suff = {"case_p1_only_p3_reaches_all": 0, "case_p1_only_all_reach_p3": 0,
        "case_p3_only_p1_reaches_all": 0, "case_p3_only_all_reach_p3": 0}
hyp = {"case_p1": 0, "case_p3": 0}
for mask in range(1 << 7):
    T = [W1[i] for i in range(7) if (mask >> i) & 1]
    C = [a for a in W1 if a not in T]
    allB = {0, 1, 2, 3}
    allreach3 = all(2 in reach_from(q, C) for q in range(4))
    if reach_from(0, T) == allB:
        hyp["case_p1"] += 1
        c1 = reach_from(2, C) == allB
        if c1 and allreach3:
            viol["case_p1"].append(T)
        if c1:
            suff["case_p1_only_p3_reaches_all"] += 1
        if allreach3:
            suff["case_p1_only_all_reach_p3"] += 1
    if reach_from(2, T) == allB:
        hyp["case_p3"] += 1
        c1 = reach_from(0, C) == allB
        if c1 and allreach3:
            viol["case_p3"].append(T)
        if c1:
            suff["case_p3_only_p1_reaches_all"] += 1
        if allreach3:
            suff["case_p3_only_all_reach_p3"] += 1
out["finite_lemma"] = {"subsets_satisfying_hypothesis": hyp, "violations": viol,
                       "single_conjunct_counts_(0_means_that_conjunct_alone_is_impossible)": suff}

# (4) cut table, entries heads {p1,p3} = {0,2}; exits tails both p3 = 2
entries = [0, 2]
cutA = {}
cutB = {}
for k in range(1, 5):
    for Y in itertools.combinations(range(4), k):
        Y = set(Y)
        cutA[str(sorted(Y))] = sum(1 for (u, v) in W1 if u not in Y and v in Y) + sum(1 for h in entries if h in Y)
        X = Y
        cutB[str(sorted(X))] = sum(1 for (u, v) in W1 if u in X and v not in X) + (2 if 2 in X else 0)
out["cut_table"] = {"A_subset_X__in_cut_of_Y_plus_entries": cutA, "min_A_case": min(cutA.values()),
                    "X_subset_B__out_cut_plus_exits": cutB, "min_B_case": min(cutB.values())}
print(json.dumps(out, indent=1, sort_keys=True))
