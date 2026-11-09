#!/usr/bin/env python3
"""Decisive calculations for r320 proposals 347483 and 327474.

(a) 347483 (Berlow, arXiv:2008.01164v2 Conjecture 5.1): exhaustive periodic-point
    search for s_{132,213} and s_{231,213} on S_n, n<=8, with implementation
    validated against the paper's proved case s_{123,132} (half-decreasing
    periodic points, Corollaries 4.6/4.7) and s_{312,321} (Corollary 4.9).
(b) 327474 (arXiv:1403.3868v2 Conjecture 6.3): compute Pr^{2n}(G) = #(a_1..a_{2n}:
    a_1...a_{2n}=a_{2n}...a_1)/|G|^{2n} for n=1,2,3 on hand-coded small groups;
    compare sequences against |G/Z(G)| to probe for a counterexample pair.
Writes work/decisive-results.json.
"""
import json, os, itertools
import numpy as np

LANE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WORK = os.path.join(LANE, "work")
os.makedirs(WORK, exist_ok=True)

def contains_pattern(w, pat):
    """True if word w (list) has a subsequence order-isomorphic to pat."""
    m = len(w); k = len(pat)
    if m < k: return False
    import itertools as it
    for idx in it.combinations(range(m), k):
        sub = [w[i] for i in idx]
        order = sorted(range(k), key=lambda i: sub[i])
        # compare relative order of sub with pat
        porder = sorted(range(k), key=lambda i: pat[i])
        if order != porder:
            return False  # wait: need ALL subsequences to be checked; fix below
    return False

def word_is_pattern(sub, pat):
    k = len(sub)
    return sorted(range(k), key=lambda i: sub[i]) == sorted(range(k), key=lambda i: pat[i])

def contains(w, pats):
    m = len(w)
    for pat in pats:
        k = len(pat)
        if m < k: continue
        for idx in itertools.combinations(range(m), k):
            if word_is_pattern([w[i] for i in idx], pat):
                return True
    return False

def s_T(perm, T):
    """Simulate s_T (Berlow Def 1.3): the stack is kept T-avoiding when read
    TOP-TO-BOTTOM; each input element is retried until it enters. Validated
    against Theorem 2.3 and Lemma 4.3 of arXiv:2008.01164v2."""
    stack = []
    out = []
    i = 0
    while i < len(perm):
        x = perm[i]
        trial = [x] + list(reversed(stack))  # stack read top-to-bottom after pushing x
        if not contains(trial, T):
            stack.append(x)
            i += 1
        else:
            out.append(stack.pop())
    out.extend(reversed(stack))
    return tuple(out)

def all_periodic(n, T, max_steps=1000):
    """Return set of periodic points of s_T on S_n via global 3-state memo:
    0 unknown, 1 on a cycle, 2 preperiodic."""
    perms = list(itertools.permutations(range(1, n + 1)))
    state = {p: 0 for p in perms}
    f = {p: s_T(p, T) for p in perms}
    for start in perms:
        if state[start] != 0: continue
        path = []
        seen = set()
        p = start
        while state[p] == 0 and p not in seen:
            seen.add(p); path.append(p); p = f[p]
        if p in seen:
            cyc_start = path.index(p)
            for q in path[cyc_start:]: state[q] = 1
            for q in path[:cyc_start]: state[q] = 2
        elif state[p] == 1:
            for q in path: state[q] = 2
        else:
            for q in path: state[q] = 2
    return {p for p in perms if state[p] == 1}

def half_decreasing(perm):
    # Def 4.2: subsequence pi(n-1) pi(n-3) ... pi(2) (odd n) / pi(3) (even n, 1-based)
    # is the identity of length floor((n-1)/2). 0-based indices n-2, n-4, ..., 1.
    n = len(perm)
    idxs = list(range(n - 2, 0, -2))
    vals = [perm[i] for i in idxs]
    return vals == list(range(1, len(idxs) + 1))

res_a = {}
# Validation: solved case T={123,132}: periodic points = half-decreasing perms (Thm 4.5)
Tval = [(1, 2, 3), (1, 3, 2)]
for n in (3, 4, 5):
    pp = all_periodic(n, Tval)
    expect = {p for p in itertools.permutations(range(1, n + 1)) if half_decreasing(p)}
    res_a[f"validate_123_132_n{n}"] = {
        "periodic_count": len(pp), "expected_half_decreasing_count": len(expect),
        "match": pp == expect}
# Corollary 4.9: periodic points of s_{312,321} = half-increasing (complements of half-decreasing)
T2v = [(3, 1, 2), (3, 2, 1)]
for n in (3, 4, 5):
    pp = all_periodic(n, T2v)
    expect = {tuple(n + 1 - v for v in p) for p in itertools.permutations(range(1, n + 1)) if half_decreasing(p)}
    res_a[f"validate_312_321_n{n}"] = {"periodic_count": len(pp), "match": pp == expect}

# Target conjecture: T1={132,213}, T2={231,213}: only identity and its reverse
T1 = [(1, 3, 2), (2, 1, 3)]
T3 = [(2, 3, 1), (2, 1, 3)]
for name, T in [("132_213", T1), ("231_213", T3)]:
    for n in range(3, 9):
        pp = all_periodic(n, T)
        ident = tuple(range(1, n + 1)); rev = tuple(range(n, 0, -1))
        extra = sorted(pp - {ident, rev})
        res_a[f"{name}_n{n}"] = {"periodic_count": len(pp), "only_id_and_reverse": pp == {ident, rev},
                                 "extra": [list(e) for e in extra]}
        print(name, n, len(pp), pp == {ident, rev}, flush=True)

# ---- (b) 327474: small-group Pr^{2n} scan ----
def group_from_cayley(elements, mul):
    """elements: list; mul: dict (x,y)->z."""
    n = len(elements)
    M = np.zeros((n, n), dtype=np.int64)
    for i, x in enumerate(elements):
        for j, y in enumerate(elements):
            M[i, j] = mul[(x, y)]
    return elements, M

def dihedral(m):  # order 2m
    els = [(i, e) for e in (0, 1) for i in range(m)]
    def mul(x, y):
        i, e = x; j, d = y
        return ((i + (j if e == 0 else -j)) % m, e ^ d)
    return els, mul

def quaternion(m):  # Q_{4m}: a^{2m}=1, a^m=b^2, b a b^{-1} = a^{-1}; order 4m
    els = [(i, e) for e in (0, 1) for i in range(2 * m)]
    def mul(x, y):
        i, e = x; j, d = y
        if e == 0 and d == 0: return ((i + j) % (2 * m), 0)
        if e == 0 and d == 1: return ((i + j) % (2 * m), 1)
        if e == 1 and d == 0: return ((i - j) % (2 * m), 1)
        return ((i - j + m) % (2 * m), 0)
    return els, mul

def semidihedral_modular(m, exp):  # order 2m: a^m=1,b^2=1, b a b^-1 = a^exp
    els = [(i, e) for e in (0, 1) for i in range(m)]
    def mul(x, y):
        i, e = x; j, d = y
        if e == 0: return ((i + j) % m, d)
        return ((i + exp * j) % m, (1 + d) % 2)
    return els, mul

def direct_product(g1, g2):
    e1, m1 = g1; e2, m2 = g2
    els = [(x, y) for x in e1 for y in e2]
    def mul(x, y):
        return (m1(x[0], y[0]), m2(x[1], y[1]))
    return els, mul

def cyclic(n):
    els = list(range(n))
    return els, lambda x, y: (x + y) % n

def pr2n(M, n):
    g = M.shape[0]
    P = np.arange(g)
    for i in range(1, 2 * n):
        P = M[P[..., None], np.arange(g)].reshape(*([g] * (i + 1)))
    R = np.transpose(P, tuple(reversed(range(P.ndim))))
    return int(np.count_nonzero(P == R)), g ** (2 * n)

def invariants(g):
    els, M = g
    e, Mt = els, M
    n = len(e)
    e_inv = {i: int(np.where(Mt[:, i] == 0)[0][0]) for i in range(n)}
    # identity index: element x with x*x=x
    ident = next(i for i in range(n) if Mt[i, i] == i)
    # conjugacy classes
    seen = set(); classes = []
    for i in range(n):
        if i in seen: continue
        cl = {int(Mt[(ident - e_inv[c]) % 0, :].sum()) for c in []}  # placeholder
        seen.add(i)
        break
    # proper conjugacy computation
    seen = set(); classes = []
    for i in range(n):
        if i in seen: continue
        cl = set()
        for c in range(n):
            # c^-1 i c
            cinv = e_inv[c]
            x = int(Mt[i, cinv]); x = int(Mt[c, x])
            cl.add(x)
        classes.append(sorted(cl)); seen |= cl
    commutator = set()
    for a in range(n):
        for b in range(n):
            ab = int(Mt[a, b]); ba = int(Mt[b, a])
            commutator.add(int(Mt[ab, e_inv[ba]]))
    center = [i for i in range(n) if len([c for c in range(n) if Mt[i, c] == Mt[c, i]]) == n]
    return {"order": n, "k": len(classes),
            "class_sizes": sorted(len(c) for c in classes),
            "gprime_order": len(commutator), "z_order": len(center)}

groups = {
    "D8": dihedral(4), "Q8": quaternion(2),
    "D8xC2": direct_product(dihedral(4), cyclic(2)),
    "Q8xC2": direct_product(quaternion(2), cyclic(2)),
    "D12": dihedral(6),
    "D16": dihedral(8), "Q16": quaternion(4),
    "SD16": semidihedral_modular(8, 3), "M16": semidihedral_modular(8, 5),
    "D8xC4": direct_product(dihedral(4), cyclic(4)),
    "Q8xC4": direct_product(quaternion(2), cyclic(4)),
    "D8xC3": direct_product(dihedral(4), cyclic(3)),
}
res_b = {}
for name, g in groups.items():
    if g is None: continue
    els, mul = g
    idx = {x: i for i, x in enumerate(els)}
    n = len(els)
    Mt = np.zeros((n, n), dtype=np.int16)
    for i, x in enumerate(els):
        for j, y in enumerate(els):
            Mt[i, j] = idx[mul(x, y)]
    inv = invariants((els, Mt))
    seq = {}
    for k in (1, 2, 3 if n <= 16 else 2):
        cnt, tot = pr2n(Mt, k)
        import math
        seq[f"Pr^{2*k}"] = f"{cnt}/{tot}"
        # reduce
        d = math.gcd(cnt, tot); seq[f"Pr^{2*k}_reduced"] = f"{cnt//d}/{tot//d}"
    res_b[name] = {**inv, **seq}
    print(name, inv, seq, flush=True)

with open(os.path.join(WORK, "decisive-results.json"), "w") as f:
    json.dump({"a_347483": res_a, "b_327474": res_b}, f, indent=1)
print("DONE")
