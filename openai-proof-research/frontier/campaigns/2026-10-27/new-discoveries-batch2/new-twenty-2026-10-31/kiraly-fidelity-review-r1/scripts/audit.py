"""Independent reviewer audit of the C11 Kiraly counterexample (written from scratch, no author code)."""
import itertools, json, sys
from fractions import Fraction

E = [{1,7,10},{2,3,8},{2,3,4},{0,3,4},{0,1,4},{0,5,6},{5,6,7},{1,6,7},{2,8,9},{8,9,10},{5,9,10}]
V = list(range(11))
out = {}

# clutter + ground-set coverage
out["clutter"] = all(not (a <= b) for a, b in itertools.permutations(E, 2))
out["distinct_edges"] = len({frozenset(e) for e in E}) == 11
out["ground_covered"] = set().union(*E) == set(V)
out["degrees"] = [sum(v in e for e in E) for v in V]

# blocker by definition over all 2^11 subsets
def transversal(T): return all(e & T for e in E)
trans = [frozenset(T) for k in range(12) for T in itertools.combinations(V, k) if transversal(set(T))]
tset = set(trans)
blk = [T for T in trans if not any((T - {v}) in tset for v in T)]
# minimality by one-element erasure is equivalent to full minimality (transversality is upward closed);
# double-check with full subset test
blk_full = [T for T in trans if not any(S < T for S in trans)]
assert set(blk) == set(blk_full)
out["blocker_size"] = len(blk)
out["blocker_size_hist"] = {k: sum(len(T) == k for T in blk) for k in sorted({len(T) for T in blk})}
out["C_cap_B_empty"] = not ({frozenset(e) for e in E} & set(blk))

# compare with Lean YL (parsed from the candidate file)
src = open(sys.argv[1], encoding="utf-8").read()
import re
def parse_list(name):
    i = src.index("def " + name)
    j = src.index("]", src.index("[{", i)) if False else None
    body = src[src.index(":=", i) + 2:]
    body = body[:body.index("\n\n")]
    return [frozenset(int(x) for x in m.split(",")) for m in re.findall(r"\{([0-9, ]+)\}", body)]
XL = parse_list("XL"); YL = parse_list("YL")
out["lean_XL_matches_edges"] = XL == [frozenset(e) for e in E]
out["lean_YL_len"] = len(YL)
out["lean_YL_distinct"] = len(set(YL)) == len(YL)
out["lean_YL_equals_full_blocker"] = set(YL) == set(blk)

# fractional vertex: exact rank of 11x11 incidence matrix
M = [[Fraction(1 if v in e else 0) for v in V] for e in E]
def rank(A):
    A = [r[:] for r in A]; r = 0
    for c in range(len(A[0])):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c] / A[r][c]; A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        r += 1
    return r
out["incidence_rank"] = rank(M)
def det(A):
    A = [r[:] for r in A]; n = len(A); d = Fraction(1)
    for c in range(n):
        p = next((i for i in range(c, n) if A[i][c] != 0), None)
        if p is None: return Fraction(0)
        if p != c: A[c], A[p] = A[p], A[c]; d = -d
        d *= A[c][c]
        for i in range(c + 1, n):
            f = A[i][c] / A[c][c]; A[i] = [a - f * b for a, b in zip(A[i], A[c])]
    return d
out["incidence_det"] = str(det(M))
xs = [Fraction(1, 3)] * 11
out["xstar_feasible"] = all(x >= 0 for x in xs) and all(sum(xs[v] for v in e) >= 1 for e in E)
out["xstar_tight_count"] = sum(sum(xs[v] for v in e) == 1 for e in E)

# Lehman structure: Bbar = 4-sets of blocker; A Bbar^T = J + I after matching
B4 = [T for T in blk if len(T) == 4]
inter = [[len(e & T) for T in B4] for e in E]
out["n_B4"] = len(B4)
out["A_B4_entries"] = sorted({x for r in inter for x in r})
out["A_B4_each_row_one_2"] = all(r.count(2) == 1 for r in inter) and all(sum(inter[i][j] == 2 for i in range(11)) == 1 for j in range(len(B4)))

# cyclic-core test: isomorphism to C_11^3 = {i,i+1,i+2 mod 11}
cyc = [frozenset({i, (i+1) % 11, (i+2) % 11}) for i in range(11)]
def pair_profile(F):
    from collections import Counter
    c = Counter(frozenset(p) for e in F for p in itertools.combinations(sorted(e), 2))
    return sorted(Counter(c.values()).items())
out["pair_profile_C11"] = pair_profile([frozenset(e) for e in E])
out["pair_profile_cyclic"] = pair_profile(cyc)
# exhaustive isomorphism check is 11! too big; use invariant + bounded backtracking
def iso(F, G):
    F = [frozenset(x) for x in F]; Gs = set(frozenset(x) for x in G)
    perm = {}
    order = V
    def ok_partial():
        for e in F:
            if all(v in perm for v in e) and frozenset(perm[v] for v in e) not in Gs: return False
        return True
    def bt(k, used):
        if k == 11: return True
        for w in V:
            if w in used: continue
            perm[order[k]] = w
            if ok_partial() and bt(k + 1, used | {w}): return True
            del perm[order[k]]
        return False
    return bt(0, frozenset())
out["isomorphic_to_cyclic_C11_3"] = iso(E, cyc)

# no (p,q): brute force over all 3^11 choices of p, q decoupled per blocker member, FULL blocker
Es = [sorted(e) for e in E]
single = {}  # (Y index) -> list of (edge idx, v) with e ∩ Y = {v}
for j, T in enumerate(blk):
    single[j] = [(i, next(iter(set(Es[i]) & T))) for i in range(11) if len(set(Es[i]) & T) == 1]
count_sat = 0; dead_hist = {}
for choice in itertools.product(range(3), repeat=11):
    p = [Es[i][choice[i]] for i in range(11)]
    feasible = True; ndead = 0
    for j, T in enumerate(blk):
        killed = {v for (i, v) in single[j] if p[i] == v}
        if killed >= T:
            feasible = False; ndead += 1
    if feasible: count_sat += 1
    dead_hist[ndead] = dead_hist.get(ndead, 0) + 1
out["p_choices"] = 3 ** 11
out["p_with_valid_q"] = count_sat
out["min_dead_blockers_over_p"] = min(dead_hist)
# same but restricted to the 36 Lean-YL members (should equal full blocker anyway)
# also Pap single-h version: since C ∩ B = ∅, h <-> (p,q); we additionally check no h exists by the same count.

# control: degenerate literal reading (q unconstrained): does a (p,q) exist for C11? (trivially yes if p misses a vertex)
img_miss = 0
for choice in itertools.product(range(3), repeat=11):
    p = {Es[i][choice[i]] for i in range(11)}
    if len(p) < 11: img_miss += 1; break
out["literal_reading_degenerate_witness_exists"] = img_miss > 0

json.dump(out, sys.stdout, indent=1, default=str); print()
