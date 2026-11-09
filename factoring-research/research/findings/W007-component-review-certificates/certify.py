"""Exact symbolic certificates for W007-component-review.md.

Standard library only.  No prime field is enumerated and no candidate is run.
Polynomials are dicts {exponent tuple: integer coefficient} over Z in the
variables (X, r_0, ..., r_{K-1}).  Every check is an exact identity in Z[...]
(hence in every commutative ring) or an exact rational closed-form identity.
"""
from fractions import Fraction
from itertools import combinations
import sys

K = 5          # number of training variables r_0..r_4
NV = K + 1     # variable 0 is X, variable 1+j is r_j


def var(i):
    e = [0] * NV
    e[i] = 1
    return {tuple(e): 1}


def const(c):
    return {tuple([0] * NV): c} if c else {}


def add(a, b, s=1):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + s * c
        if out[m] == 0:
            del out[m]
    return out


def mul(a, b):
    out = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = tuple(x + y for x, y in zip(m1, m2))
            out[m] = out.get(m, 0) + c1 * c2
            if out[m] == 0:
                del out[m]
    return out


def subst_X(a, v):
    """Substitute X := variable v (v != 0)."""
    out = {}
    for m, c in a.items():
        mm = list(m)
        mm[v] += mm[0]
        mm[0] = 0
        mm = tuple(mm)
        out[mm] = out.get(mm, 0) + c
        if out[mm] == 0:
            del out[mm]
    return out


def zero_vars(a, vs):
    return {m: c for m, c in a.items() if all(m[v] == 0 for v in vs)}


def degs(a):
    return {sum(m) for m in a}


def deg_in(a, v):
    return max(m[v] for m in a)


def involves(a, v):
    return any(m[v] for m in a)


def lead_in(a, v):
    d = deg_in(a, v)
    return {m: c for m, c in a.items() if m[v] == d}, d


X = var(0)
r = [var(1 + j) for j in range(K)]

# Tower P_0..P_K with a_j = P_j(r_j).
P = [X]
for j in range(K):
    a_j = subst_X(P[j], 1 + j)
    P.append(mul(P[j], add(P[j], a_j, -1)))

report = []

# 1. Homogeneity of degree 2^m, monic in X, and P_m(X; 0) = X^(2^m).
for m in range(K + 1):
    assert degs(P[m]) == {2 ** m}, m
    lt, d = lead_in(P[m], 0)
    assert d == 2 ** m and lt == {tuple([d] + [0] * K): 1}, m
    z = zero_vars(P[m], range(1, NV))
    assert z == {tuple([2 ** m] + [0] * K): 1}, m
report.append("P_m homogeneous of total degree 2^m, monic in X, P_m(X;0)=X^(2^m), m<=%d" % K)


def Q(i, j):
    return add(add(P[i], subst_X(P[i], 1 + j)), subst_X(P[i], 1 + i), -1)


# 2. Factorization (1) for k <= 4 as an identity in Z[X, r].
for k in range(0, 5):
    prod = X
    for j in range(k):
        prod = mul(prod, add(X, r[j], -1))
    for i, j in combinations(range(k), 2):
        prod = mul(prod, Q(i, j))
    assert prod == P[k], k
report.append("identity (1) P_k = X prod(X-r_j) prod Q_(i,j) exact over Z for k<=4")

# 3. Each Q_(i,j), i>=1, homogeneous of degree 2^i, specialises to Fermat form.
for i, j in combinations(range(K), 2):
    q = Q(i, j)
    assert degs(q) == {2 ** i}
    f = zero_vars(q, range(1, 1 + i))
    D = 2 ** i
    ferm = {}
    for v, s in ((0, 1), (1 + j, 1), (1 + i, -1)):
        e = [0] * NV
        e[v] = D
        ferm[tuple(e)] = s
    assert f == ferm, (i, j)
report.append("Q_(i,j) homogeneous of degree 2^i; r_0..r_(i-1)=0 gives X^D+r_j^D-r_i^D, all i<j<%d" % K)

# 4. Pairwise elimination lemma inputs: for every pair of distinct factors of
#    P_k (k=K) there is u != X with F = +-(u^deg F + lower in u) and G free of u.
k = K
factors = [("X", X)] + [("X-r%d" % j, add(X, r[j], -1)) for j in range(k)]
factors += [("Q%d,%d" % (i, j), Q(i, j)) for i, j in combinations(range(k), 2)]
for name, F in factors:
    lt, d = lead_in(F, 0)
    assert d == max(degs(F)) and list(lt.values()) == [1], name   # monic in X, X-degree = total degree


def eliminator(F, G):
    dF = max(degs(F))
    for u in range(1, NV):
        if involves(G, u) or not involves(F, u):
            continue
        lt, d = lead_in(F, u)
        if d == dF and len(lt) == 1 and abs(next(iter(lt.values()))) == 1:
            return u
    return None


pairs = 0
for (n1, F), (n2, G) in combinations(factors, 2):
    assert F != G
    u = eliminator(F, G)
    if u is None:
        u = eliminator(G, F)
    assert u is not None, (n1, n2)
    pairs += 1
report.append("elimination variable exists for all %d pairs of the %d factors at k=%d" % (pairs, len(factors), k))

# 5. Closed forms (exact integer/rational identities) for 0<=k<=60.
for k in range(0, 61):
    L = 1 + k * (k + 1) // 2
    dlist = [1] * (1 + k) + [2 ** i for j in range(k) for i in range(j)]
    assert len(dlist) == L and sum(dlist) == 2 ** k
    B = sum((k - 1 - i) * (2 ** i - 1) ** 2 for i in range(0, k - 1))
    assert 9 * B == (4 ** k - 3 * k - 1) - 18 * (2 ** k - k - 1) + 9 * k * (k - 1) // 2 * 1, k
    Pi = (sum(dlist) ** 2 - sum(d * d for d in dlist)) // 2
    assert 9 * Pi == 4 ** (k + 1) - 3 * k - 4, k
    assert 2 * Pi <= 4 ** k
    A = sum((k - 1 - i) * (i + 1) * (2 ** i - 1) for i in range(1, k - 1))
    assert 6 * A == 6 * (k - 3) * 2 ** k + 6 * (k + 3) - (k ** 3 - k), k
    assert A <= k * 2 ** k
    lin = sum(1 for d in dlist if d == 1)
    assert lin == (2 * k if k >= 1 else 1)
report.append("closed forms L_k, sum deg=2^k, B_k, Pi_k=(4^(k+1)-3k-4)/9, A_k=(k-3)2^k+k+3-(k^3-k)/6, linear count, 0<=k<=60")

# 6. Arithmetic used in the regime induction: sum_(l=1)^(i-1) (l+1) 2^l = (i-1) 2^i.
for i in range(1, 80):
    assert sum((l + 1) * 2 ** l for l in range(1, i)) == (i - 1) * 2 ** i
report.append("sum_(l=1)^(i-1)(l+1)2^l=(i-1)2^i for 1<=i<80")

print("\n".join("PASS " + s for s in report))
