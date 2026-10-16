#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Independent algebra for the K_n-e manuscript audit. Not a proof.

Integer division and fractions.Fraction only. Re-derives closed forms,
OWH gap identities, the n=1 product reduction, and a small two-page count.
Does not import the manuscript checkers.
"""
import itertools
from fractions import Fraction as Fr
from math import comb

FAILURES = []


def check(ok, detail):
    if not ok:
        FAILURES.append(detail)
        print("FAIL", detail)


def Z(n):
    return (n // 2) * ((n - 1) // 2) * ((n - 2) // 2) * ((n - 3) // 2) // 4


def target(n):
    return Z(n) - comb((n - 1) // 2, 2)


def floor_product(n):
    return ((n + 2) // 2) * ((n - 1) // 2) * ((n - 3) // 2) * ((n - 4) // 2)


def zheng4(m, n):
    return ((m + 1) // 2) * ((m - 1) // 2) * ((m - 2) // 2) * (
        n * ((m + 4) // 2) + (m - 4) // 2
    )


def ceil_div(a, b):
    return -((-a) // b)


def sym_dim(s):
    # exponents 0..s-2, basis x^a u^b + x^b u^a for a<b and x^a u^a
    k = s - 1
    return k * (k + 1) // 2


def main():
    owh_minus = {4: 0, 5: 0, 6: 2, 7: 6, 8: 15, 9: 30, 10: 54, 11: 90, 12: 140}
    owh_complete = {4: 0, 5: 1, 6: 3, 7: 9, 8: 18, 9: 36, 10: 60, 11: 100, 12: 150}
    for n, value in owh_complete.items():
        check(Z(n) == value, f"Z({n})")
    for n, value in owh_minus.items():
        check(target(n) == value, f"target({n})")

    for n in range(2, 2001):
        prod4 = (n // 2) * ((n - 1) // 2) * ((n - 2) // 2) * ((n - 3) // 2)
        check(prod4 % 4 == 0, f"Z divisible n={n}")
        check(4 * target(n) == floor_product(n), f"floor n={n}")
        s = n // 2
        if n % 2:
            check(target(n) == comb(s, 2) ** 2 - comb(s, 2), f"odd n={n}")
        else:
            check(4 * target(n) == (s * s - 1) * (s - 2) ** 2, f"even n={n}")
        if n <= 5:
            check(target(n) == 0, f"small n={n}")
        if n >= 6 and n % 2 == 0:
            check((n + 2) * Z(n - 1) == (n - 2) * target(n), f"even identity n={n}")

    for s in range(2, 40):
        check(sym_dim(s) == comb(s, 2), f"sym dim s={s}")

    closes = []
    for n in range(5, 401, 2):
        s = (n - 1) // 2
        numerator = 2 * Z(n - 1) + (n - 2) * (Z(n) - (n - 3) // 2)
        deficit = Fr(target(n)) - Fr(numerator, n)
        check(deficit == Fr((s - 1) * (s - 2), 2 * (2 * s + 1)), f"3.1 deficit n={n}")
        check((s - 1) * (s - 2) - 2 * (2 * s + 1) == s * (s - 7), f"deficit sign n={n}")
        if ceil_div(numerator, n) == target(n):
            closes.append(n)
        if s >= 3:
            gap32 = Fr(target(n)) - Fr((n + 2) * Z(n - 1), n - 2)
            check(gap32 == Fr(s * (s - 1) * (s - 2), 2 * (2 * s - 1)), f"3.2 gap n={n}")
            avg_num = 2 * Z(2 * s) + (2 * s - 1) * target(2 * s)
            gap_avg = Fr(target(n)) - Fr(avg_num, 2 * s - 3)
            check(
                gap_avg == Fr((s - 1) ** 2 * (s - 2), 2 * (2 * s - 3)),
                f"deletion gap n={n}",
            )
    check(closes == [5, 7, 9, 11, 13], f"integrality closes {closes}")
    check(ceil_div(2 * Z(14) + 13 * (Z(15) - 6), 15) == 419, "n=15 ceiling")
    check(target(15) == 420, "n=15 target")
    check(Fr(2 * Z(12) + 11 * (Z(13) - 5), 13) == Fr(2720, 13), "n=13 bound")

    for m in range(4, 201):
        for n in range(1, 21):
            via = 4 * ((n - 1) * target(m + 2) + 2 * Z(m + 1))
            check(via == zheng4(m, n), f"corollary m={m} n={n}")
        # n=1 drops the minus-edge term for every m, including odd m>=13.
        check(zheng4(m, 1) == 8 * Z(m + 1), f"n=1 is 2 Z(m+1) m={m}")
        check(
            (0 * (target(m + 2) - 1) + 2 * Z(m + 1)) == 2 * Z(m + 1),
            f"n=1 insensitive m={m}",
        )
        if m % 2 == 1 and m >= 13 and n_uses_new(m):
            changed = (1 * (target(m + 2) - 1) + 2 * Z(m + 1))
            exact = (1 * target(m + 2) + 2 * Z(m + 1))
            check(exact - changed == 1, f"n=2 uses minus-edge m={m}")

    check(target(15) == 420 and Z(14) == 315, "explicit 15/14")
    check(2 * Z(14) == 630, "m=13 n=1 value 630")
    check(target(15) + 2 * Z(14) == 1050, "m=13 n=2 value 1050")
    check(419 + 2 * Z(14) == 1049, "counting ceiling misses product by 1 at m=13,n=2")
    check(zheng4(4, 1) == 8 and zheng4(4, 7) == 4 * 14, "m=4 gives 2n")

    # two-page deletion, independent of release_checks.r2, for 4<=n<=30
    for n in range(4, 31):
        m = n // 2
        edges = [(i, j) for i in range(n) for j in range(i + 1, n)]
        page = {e: ((e[0] + e[1]) % n) < m for e in edges}
        total = 0
        on_deleted = 0
        t = (n - 1) // 2
        deleted = (0, t)
        for (i, j), (k, l) in itertools.combinations(edges, 2):
            if page[(i, j)] != page[(k, l)] or len({i, j, k, l}) < 4:
                continue
            if (i < k < j < l) or (k < i < l < j):
                total += 1
                if deleted in ((i, j), (k, l)):
                    on_deleted += 1
        check(total == Z(n), f"two-page total n={n}")
        check(on_deleted == comb(t, 2), f"deleted edge n={n}")
        check(total - on_deleted == target(n), f"remaining n={n}")

    print("independent algebra", "PASS" if not FAILURES else f"FAIL {len(FAILURES)}")
    return 0 if not FAILURES else 1


def n_uses_new(m):
    return True


if __name__ == "__main__":
    raise SystemExit(main())
