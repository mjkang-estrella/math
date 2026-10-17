#!/usr/bin/env python3
"""MIT; Myeongjin Kang. Exact guards for CS; not a proof of the sampler."""
from fractions import Fraction as Q
from itertools import permutations
import json


def det(a):
    if not a:
        return Q(1)
    return sum(((-1) ** j * a[0][j] * det(
        [row[:j] + row[j+1:] for row in a[1:]])
        for j in range(len(a))), Q(0))


def dpp(k):
    n = len(k)
    inc = {}
    for mask in range(1 << n):
        s = [i for i in range(n) if mask >> i & 1]
        inc[mask] = det([[k[i][j] for j in s] for i in s])
    law = {a: sum(((-1) ** (b.bit_count()-a.bit_count()) * inc[b]
                   for b in inc if b & a == a), Q(0)) for a in inc}
    assert min(law.values()) >= 0 and sum(law.values()) == 1
    return law


def expect(law, f):
    return sum((p * f(a) for a, p in law.items()), Q(0))


def cov(law, i, j):
    return (expect(law, lambda a: (a >> i & 1) * (a >> j & 1))
            - expect(law, lambda a: a >> i & 1)
            * expect(law, lambda a: a >> j & 1))


def ball(c, i, n):
    seen = {i}
    for _ in range(n):
        new = seen | {j for a in seen for j in range(len(c))
                      if a != j and c[a][j] >= Q(1, n)}
        if new == seen:
            break
        seen = new
    return seen


def main():
    # Eigenvalues lie in [3/10,7/10] by the elementary row-sum bound.
    k = [[Q(1, 2), Q(1, 10), Q(0)],
         [Q(1, 10), Q(1, 2), Q(1, 10)],
         [Q(0), Q(1, 10), Q(1, 2)]]
    law = dpp(k)
    assert cov(law, 0, 2) == 0
    conditional = {a: p * 2 for a, p in law.items() if a >> 1 & 1}
    assert sum(conditional.values()) == 1
    assert cov(conditional, 0, 2) == -Q(1, 2500)
    c = [[-cov(law, i, j) if i != j else Q(0)
          for j in range(3)] for i in range(3)]
    assert c[0][1] == c[1][2] == Q(1, 100)
    assert ball(c, 0, 99) == {0}
    assert ball(c, 0, 100) == {0, 1, 2}
    relabel_checks = 0
    for perm in permutations(range(3)):
        cp = [[Q(0)] * 3 for _ in range(3)]
        for i in range(3):
            for j in range(3):
                cp[perm[i]][perm[j]] = c[i][j]
        for n in [1, 4, 99, 100, 101]:
            for i in range(3):
                assert ball(cp, perm[i], n) == {perm[j] for j in ball(c, i, n)}
                relabel_checks += 1
    # Pairwise independence without NA must not trigger the component argument.
    parity = {0: Q(1, 4), 3: Q(1, 4), 5: Q(1, 4), 6: Q(1, 4)}
    assert all(cov(parity, i, j) == 0 for i in range(3) for j in range(i))
    e = lambda a: a & 1
    f = lambda a: int(bool(a & 6))
    gap = expect(parity, lambda a: e(a)*f(a)) - expect(parity,e)*expect(parity,f)
    assert gap == Q(1, 8)
    print(json.dumps({"status": "EXACT_DIAGNOSTICS_PASS", "relabel_checks": relabel_checks,
                      "zero_pair_conditional_covariance": str(cov(conditional,0,2)),
                      "non_NA_parity_gap": str(gap),
                      "full_sampler_verified": False}, indent=2))


if __name__ == "__main__":
    main()
