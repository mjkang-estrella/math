#!/usr/bin/env python3
"""Subagent F -- Task 3: the level-1 exponential-Diophantine test for
m0 = 2^a * 3^b * 7^d, by bounded arrangement enumeration.

THE EQUATION.  Fix m0 = 2^a 3^b 7^d (Theorem A: a*c = 0, so no factor 5) and
let F(a,b) be the min-lex minimal factorization of 2^a 3^b (Theorem C.2).
Every preimage n of m0 whose digits are exactly the rigid multiset
{7^d} u F(a,b) plus j inserted 1s is, by Fonga's Lemma 2.1,

    n = (10^L - 1)/9 + SUM_i (d_i - 1) 10^{r_i},   L = len23(a,b) + d + j,

where the k = len23(a,b) + d exceptional digits d_1..d_k occupy pairwise
distinct positions 0 <= r_1, ..., r_k < L; equivalently, in the 9n form,

    9n = 10^L - 1 + SUM_i 9(d_i - 1) 10^{r_i}.

The level-1 chain condition (n itself 7-smooth, so that P(n) = 1 + P(m0) and
the min-lex factorization of n is a persistence-12 number) is exactly the
exponential-Diophantine equation

    (10^L - 1)/9 + SUM_i (d_i - 1) 10^{r_i} = 2^A * 3^B * 7^D

in the insertion positions (Fonga eq.-19 shape:
10^L - 1 + SUM 9(d_i-1)10^{r_i} = 2^A 3^{B+2} 7^D).

THE GENERATOR.  For a GIVEN (a, b, d, j) this script enumerates the first
SAMPLE = 2000 arrangements in sorted (ascending) order, factors each by trial
division with the primes 2,3,5,...,97 (pure stdlib), and reports any 7-smooth
member.  Default run: the record case m0 = 2^19 3^4 7^6 (digits
{2, 7^6, 8^6, 9^2} + 1s) for j = 0..6.

Usage:  python3 src/level1_diophantine.py [a b d j_lo j_hi]
"""
from __future__ import annotations

import sys
import time
from itertools import islice
from math import factorial

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from persistence import len23_table  # read-only shared library

T0 = time.time()
SAMPLE = 2000
PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
          67, 71, 73, 79, 83, 89, 97]


# ---------------------------------------------------------------------------
def F_ab(a: int, b: int) -> dict[int, int]:
    """F(a,b): the sorted lex-smallest minimal-length factorization of 2^a 3^b
    (Theorem C.2, even family).  Returns digit -> multiplicity."""
    if b % 2 == 0:
        if a % 3 == 0:
            return {8: a // 3, 9: b // 2}
        if a % 3 == 1:
            return {2: 1, 8: (a - 1) // 3, 9: b // 2}
        return {4: 1, 8: (a - 2) // 3, 9: b // 2}
    else:
        if a % 3 == 0:
            return {3: 1, 8: a // 3, 9: (b - 1) // 2}
        if a % 3 == 1:
            return {6: 1, 8: (a - 1) // 3, 9: (b - 1) // 2}
        return {2: 1, 6: 1, 8: (a - 2) // 3, 9: (b - 1) // 2}


def exceptional_digits(a: int, b: int, d: int) -> list[int]:
    exc: list[int] = []
    for digit, mult in sorted({7: d, **F_ab(a, b)}.items()):
        exc += [digit] * mult
    return exc


def arrangements(digits: str):
    """All distinct permutations of the sorted string `digits`, ascending."""
    counts: dict[str, int] = {}
    for c in digits:
        counts[c] = counts.get(c, 0) + 1
    keys = sorted(counts)
    n = len(digits)
    cur: list[str] = []

    def rec():
        if len(cur) == n:
            yield int("".join(cur))
            return
        for k in keys:
            if counts[k]:
                counts[k] -= 1
                cur.append(k)
                yield from rec()
                cur.pop()
                counts[k] += 1

    yield from rec()


def factor97(n: int):
    """Trial division by primes <= 97.  Returns (fac, cofactor); n is
    7-smooth iff fac has support in {2,3,5,7} and cofactor == 1."""
    fac: dict[int, int] = {}
    for p in PRIMES:
        while n % p == 0:
            fac[p] = fac.get(p, 0) + 1
            n //= p
    return fac, n


def fac_str(fac: dict[int, int], cof: int) -> str:
    s = "*".join(f"{p}^{k}" if k > 1 else str(p) for p, k in sorted(fac.items()))
    return s if cof == 1 else f"{s}*{cof}"


def equation_str(a: int, b: int, d: int) -> str:
    """The concrete 9n equation for this (a,b,d)."""
    exc = exceptional_digits(a, b, d)
    terms = []
    for dd in sorted(set(exc)):
        m = exc.count(dd)
        c = 9 * (dd - 1)
        terms.append(f"{c}*10^r" if m == 1 else f"{c}*sum_(i=1..{m}) 10^r_i")
    return f"10^L - 1 + {' + '.join(terms)} = 2^A * 3^(B+2) * 7^D"


# ---------------------------------------------------------------------------
def run_case(a: int, b: int, d: int, j: int, table) -> dict:
    m0 = 2 ** a * 3 ** b * 7 ** d
    exc_list = exceptional_digits(a, b, d)
    # sanity: product of exceptional digits == m0, and |F(a,b)| == len23(a,b)
    prod = 1
    for x in exc_list:
        prod *= x
    assert prod == m0, (prod, m0)
    nF = len(exc_list) - d
    assert nF == table[a][b], (nF, table[a][b])

    digit_str = "".join(sorted("1" * j + "".join(map(str, exc_list))))
    L = len(digit_str)
    total = factorial(L)
    for c in set(digit_str):
        total //= factorial(digit_str.count(c))

    smooth_hits = []
    max_v2 = max_v3 = -1
    min_cof = None
    checked = 0
    for n in islice(arrangements(digit_str), SAMPLE):
        checked += 1
        p = 1
        for ch in str(n):          # digit product must be m0 (1s contribute 1)
            p *= int(ch)
        assert p == m0
        fac, cof = factor97(n)
        max_v2 = max(max_v2, fac.get(2, 0))
        max_v3 = max(max_v3, fac.get(3, 0))
        if cof == 1 and set(fac) <= {2, 3, 5, 7}:
            smooth_hits.append(n)
        if min_cof is None or cof < min_cof:
            min_cof = cof
    return {
        "a": a, "b": b, "d": d, "j": j, "L": L, "m0": m0,
        "total_arrangements": total, "sampled": checked,
        "smooth": smooth_hits, "max_v2": max_v2, "max_v3": max_v3,
        "min_cofactor": min_cof,
    }


def main():
    args = sys.argv[1:]
    if args:
        a, b, d, j_lo, j_hi = map(int, args)
    else:
        a, b, d, j_lo, j_hi = 19, 4, 6, 0, 6
    m0 = 2 ** a * 3 ** b * 7 ** d
    print(f"LEVEL-1 DIOPHANTINE TEST  m0 = 2^{a}*3^{b}*7^{d} = {m0}")
    print(f"(the record holder's digit product: Pi(277777788888899) = 2^{a}*3^{b}*7^{d})")
    exc_list = exceptional_digits(a, b, d)
    print(f"rigid multiset {{7^{d}}} u F({a},{b}) u {{1^j}};  F({a},{b}) = {F_ab(a, b)};")
    print(f"exceptional digits (k = {len(exc_list)}): {exc_list}")
    table = len23_table(240, 160)
    print(f"check: len23({a},{b}) = {table[a][b]} = |F({a},{b})| "
          f"(Theorem C.2 length-efficiency); len(m0) = {table[a][b]} + {d} "
          f"= {table[a][b] + d}")
    print()
    print(f"9n form of the equation:  {equation_str(a, b, d)}")
    print(f"over distinct positions r in [0, L), L = {table[a][b]} + {d} + j.")
    print()

    results = []
    for j in range(j_lo, j_hi + 1):
        r = run_case(a, b, d, j, table)
        results.append(r)
        note = ""
        if r["smooth"]:
            note = f"  *** {len(r['smooth'])} 7-SMOOTH MEMBER(S): {r['smooth'][:5]}"
        print(f"j={j}: L={r['L']:>2}, total arrangements = {r['total_arrangements']:>16,}, "
              f"sampled first {r['sampled']}, 7-smooth: {len(r['smooth'])}, "
              f"max v2(sample) = {r['max_v2']}, max v3(sample) = {r['max_v3']}, "
              f"min cofactor = {r['min_cofactor']}{note}")
        if j == 0:
            smallest = int("".join(sorted("".join(map(str, exc_list)))))
            print(f"        (lex-smallest j=0 arrangement = {smallest} "
                  f"{'= the record holder 277777788888899 itself' if smallest == 277777788888899 else 'CHECK!'})")
    print()
    smooth_total = sum(len(r["smooth"]) for r in results)
    print(f"TOTAL 7-smooth members found: {smooth_total} "
          f"(out of {sum(r['sampled'] for r in results):,} sampled arrangements, "
          f"j = {j_lo}..{j_hi})")
    if smooth_total == 0:
        print(f"-> no member of the rigid family (j <= {j_hi}, first {SAMPLE} "
              "arrangements each) is 7-smooth: the level-1 Diophantine equation "
              "has NO solution in this range, cross-checking subagent C's "
              "len <= 30 exhaustion from the other direction.")
    print(f"[{time.time() - T0:.1f}s]")
    return results


if __name__ == "__main__":
    main()
