"""Independent finite certificate for the 347138 refutation (no imports from other lane scripts).

Gadget H on B = {0,1,2,3}: arcs 0->1, 1->2, 2->3, 3->0 (4-cycle), chord 0->2, 2-cycle 1<->3.
Attachments in D_m (A = complete digraph on a_0..a_{m-1}, m >= 2):
  entries a_0 -> 0, a_1 -> 2 ;  exits 2 -> a_0, 2 -> a_{m-1} (two distinct A heads).
Claims checked here (all finite, independent of m):
 (C1) every out-branching T of H rooted at 0 leaves H - T NOT strongly connected;
 (C2) every out-branching T of H rooted at 2 fails: in H - T either 0 does not reach all of B
      or some vertex of B does not reach 2;
 (C3) cut condition for lambda >= 2 for every X with A subset X or X subset B (finite in B);
 (C4) H is semicomplete (so A and B are cliques of the underlying graph, alpha = 2).
"""
import itertools, json

B = range(4)
H = {(0, 1), (1, 2), (2, 3), (3, 0), (0, 2), (1, 3), (3, 1)}
entries_into = {0: 1, 2: 1}   # number of A->B arcs into each B vertex
exits_from = {2: 2}           # number of B->A arcs out of each B vertex


def reach(arcs, s, rev=False):
    seen = {s}
    st = [s]
    while st:
        x = st.pop()
        for (u, v) in arcs:
            a, b = (v, u) if rev else (u, v)
            if a == x and b not in seen:
                seen.add(b)
                st.append(b)
    return seen


def out_branchings(arcs, r):
    others = [v for v in B if v != r]
    choices = [[u for (u, w) in arcs if w == v] for v in others]
    for pick in itertools.product(*choices):
        par = dict(zip(others, pick))
        ok = True
        for v in others:
            seen = set()
            w = v
            while w != r:
                if w in seen:
                    ok = False
                    break
                seen.add(w)
                w = par[w]
            if not ok:
                break
        if ok:
            yield {(par[v], v) for v in others}


res = {}
c1 = []
for T in out_branchings(H, 0):
    R = H - T
    strong = reach(R, 0) == set(B) and reach(R, 0, rev=True) == set(B)
    c1.append((sorted(T), strong))
res['C1_branchings_from_0'] = len(c1)
res['C1_holds'] = all(not s for _, s in c1)
c2 = []
for T in out_branchings(H, 2):
    R = H - T
    good = reach(R, 0) == set(B) and reach(R, 2, rev=True) == set(B)
    c2.append((sorted(T), good))
res['C2_branchings_from_2'] = len(c2)
res['C2_holds'] = all(not g for _, g in c2)
# C3: X = A u Y (Y proper subset of B): out-arcs = entries into B\Y + H-arcs Y -> B\Y
#     X = Y (Y nonempty subset of B): out-arcs = H-arcs Y -> B\Y + exits from Y
worst = []
for k in range(0, 5):
    for Y in itertools.combinations(B, k):
        Y = set(Y)
        Z = set(B) - Y
        internal = sum(1 for (u, v) in H if u in Y and v in Z)
        if Z:  # X = A u Y proper
            worst.append(('A+' + str(sorted(Y)), internal + sum(entries_into.get(v, 0) for v in Z)))
        if Y:  # X = Y, complement contains A
            worst.append((str(sorted(Y)), internal + sum(exits_from.get(v, 0) for v in Y)))
res['C3_min_outdegree_of_cuts'] = min(w for _, w in worst)
res['C3_holds'] = res['C3_min_outdegree_of_cuts'] >= 2
res['C4_semicomplete'] = all((u, v) in H or (v, u) in H for u in B for v in B if u < v)
print(json.dumps(res, indent=1))
print('C1 detail', c1)
print('C2 detail', c2)
