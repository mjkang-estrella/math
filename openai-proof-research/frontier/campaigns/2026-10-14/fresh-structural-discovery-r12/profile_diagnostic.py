"""Exact support for one four-orbit profile diagnostic, not a Q4 checker.
Myeongjin Kang; no affiliation. Original code MIT.
No files, imports from this package, randomness, or network.
"""
from fractions import Fraction as F
import json


def zero(n=4):
    return [[F(0) for _ in range(n)] for _ in range(n)]


def eye(n=4):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def add(a, b):
    return [[x + y for x, y in zip(r, s)] for r, s in zip(a, b)]


def scale(c, a):
    return [[c * x for x in r] for r in a]


def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def transpose(a):
    return list(map(list, zip(*a)))


def trace(a):
    return sum(a[i][i] for i in range(len(a)))


def rank(a):
    a = [r[:] for r in a]
    h = 0
    for j in range(len(a[0])):
        k = next((k for k in range(h, len(a)) if a[k][j]), None)
        if k is None:
            continue
        a[h], a[k] = a[k], a[h]
        v = a[h][j]
        a[h] = [x / v for x in a[h]]
        for k in range(len(a)):
            if k != h:
                v = a[k][j]
                if v:
                    a[k] = [x - v * y for x, y in zip(a[k], a[h])]
        h += 1
        if h == len(a):
            break
    return h


def quat_product(a, b):
    if a == 0:
        return 1, b
    if b == 0:
        return 1, a
    if a == b:
        return -1, 0
    if (a, b) in [(1, 2), (2, 3), (3, 1)]:
        return 1, 6 - a - b
    return -1, 6 - a - b


def quaternion_map(q, left):
    a = zero()
    for j in range(4):
        s, i = quat_product(q, j) if left else quat_product(j, q)
        a[i][j] = F(s)
    return a


def intertwiner_rank(pairs):
    # Each equation is M X - X N = 0 on all sixteen entries of X.
    rows = []
    for m, n in pairs:
        for i in range(4):
            for j in range(4):
                r = [F(0)] * 16
                for k in range(4):
                    r[4 * k + j] += m[i][k]
                    r[4 * i + k] -= n[k][j]
                rows.append(r)
    return rank(rows)


li, lj = quaternion_map(1, True), quaternion_map(2, True)
ri, rj = quaternion_map(1, False), quaternion_map(2, False)
i4 = eye()
for x in (li, lj, ri, rj):
    assert mul(x, x) == scale(-1, i4)
    assert transpose(x) == scale(-1, x)
for x in (li, lj):
    for y in (ri, rj):
        assert mul(x, y) == mul(y, x)

a = add(li, scale(2, ri))
b = add(lj, scale(2, rj))
c = add(add(scale(F(3, 5), li), scale(F(4, 5), lj)), scale(2, rj))
for x in (a, b, c):
    assert transpose(x) == scale(-1, x)
    x2 = mul(x, x)
    assert add(add(mul(x2, x2), scale(10, x2)), scale(9, i4)) == zero()
    assert trace(x2) == -20

ranks = [intertwiner_rank([(a, a), (b, b)]),
         intertwiner_rank([(a, a), (c, c)]),
         intertwiner_rank([(a, a), (c, b)])]
assert ranks == [15, 15, 16]
assert trace(mul(a, b)) == 0
assert trace(mul(a, c)) == F(-12, 5)
assert intertwiner_rank([(a, a), (b, b)]) < 16  # identity intertwines

levels = [-3, -1, 1, 3]
cross_ties = sum(F(x == y, 2) for _ in range(4)
                 for x in levels for y in levels)
comparisons = F(4 * 4, 2)
assert cross_ties == comparisons == 8
assert not (comparisons > cross_ties)  # reject the blind strict-count extension

print(json.dumps({
    "status": "EXACT_ONE_PROFILE_DIAGNOSTIC_ONLY",
    "target_Q4": "UNRESOLVED",
    "matrix_size_per_block": 4,
    "centralizer_and_cross_ranks": ranks,
    "trace_AB": "0",
    "trace_AC": "-12/5",
    "four_profile_cross_ties": str(cross_ties),
    "cross_comparison_count": str(comparisons),
    "strict_count_extension_rejected": True,
    "limits": "Not an exceptional odd-parity schedule; not a Q4 counterexample."
}, sort_keys=True))
