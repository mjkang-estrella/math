#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License; see ../RIGHTS.md.
"""Exact finite arithmetic checks. No asymptotic or proof certification."""
from fractions import Fraction
from itertools import combinations, product
from math import comb, gcd, prod
import json


def crt(residues, primes):
    modulus = prod(primes)
    return sum(a * (modulus // p) * pow(modulus // p, -1, p)
               for a, p in zip(residues, primes)) % modulus


def survivors(primes, forbidden, start, length):
    return [n for n in range(start, start + length)
            if all(n % p not in roots for p, roots in zip(primes, forbidden))]


def cyclic_gap(values, modulus):
    assert values
    return max(b - a for a, b in zip(values, values[1:] + [values[0] + modulus]))


def run():
    counts = {"systems": 0, "crt_positions": 0, "interval_counts": 0,
              "tree_identities": 0, "weight_identities": 0,
              "factor_mass_identities": 0, "squarefree_examples": 0}
    maxima = []
    # Saturated local pairs dominate every proper set of at most two roots.
    # These are only specified prime sets, not the maximum over all prime sets.
    for primes in ([2], [2, 3], [2, 3, 5], [2, 3, 5, 7], [3, 5, 7]):
        modulus = prod(primes)
        options = [[(a,) for a in range(2)] if p == 2
                   else list(combinations(range(p), 2)) for p in primes]
        maximum = 0
        for forbidden in product(*options):
            counts["systems"] += 1
            vals = survivors(primes, forbidden, 0, modulus)
            maximum = max(maximum, cyclic_gap(vals, modulus))
            first = [roots[0] for roots in forbidden]
            second = [roots[-1] for roots in forbidden]
            shift = crt(first, primes)
            delta = crt([(b - a) % p for p, a, b in zip(primes, first, second)], primes)
            if modulus % 2 == 0:
                assert delta % 2 == 0
            for n in range(modulus):
                original = all(n % p not in roots for p, roots in zip(primes, forbidden))
                canonical = gcd((n - shift) * (n - shift - delta), modulus) == 1
                assert original == canonical
                counts["crt_positions"] += 1
            density = prod(Fraction(p - len(r), p) for p, r in zip(primes, forbidden))
            assert len(vals) == modulus * density
            assert density >= Fraction(1, (len(primes) + 1) * (len(primes) + 2))
            # Uniform endpoint error by expanded CRT intersections.
            for start, length in [(-3, 0), (-8, 13), (0, 17), (modulus - 2, 11)]:
                s = len(survivors(primes, forbidden, start, length))
                assert abs(s - length * density) <= prod(1 + len(r) for r in forbidden)
                counts["interval_counts"] += 1
        maxima.append({"primes": primes, "max_cyclic_gap": maximum})

    # Exact least-bad-prime partition with two roots, arbitrary node and cutoff.
    primes = [3, 5, 7]
    forbidden = [(0, 1), (1, 3), (2, 5)]
    for start in [-12, 0, 7]:
        for length in [0, 1, 8, 31]:
            interval = range(start, start + length)
            for mask in range(1 << len(primes)):
                forced = [i for i in range(len(primes)) if mask >> i & 1]
                for cutoff in range(len(primes) + 1):
                    available = [i for i in range(cutoff) if i not in forced]
                    node = [n for n in interval if all(n % primes[i] in forbidden[i] for i in forced)]
                    exact = sum(all(n % primes[i] not in forbidden[i] for i in available) for n in node)
                    children = sum(sum(n % primes[i] in forbidden[i]
                                       and all(n % primes[j] not in forbidden[j]
                                               for j in available if j < i)
                                       for n in node) for i in available)
                    assert exact == len(node) - children
                    counts["tree_identities"] += 1

    # Averaging a chosen single forbidden label gives 2^{-number of hits},
    # rather than the indicator of avoiding both labels.
    for length in range(1, 32):
        lhs = sum(len(survivors(primes, [(r[s],) for r, s in zip(forbidden, sigma)], 0, length))
                  for sigma in product([0, 1], repeat=3))
        rhs = sum(2 ** (3 - sum(n % p in r for p, r in zip(primes, forbidden)))
                  for n in range(length))
        assert lhs == rhs
        counts["weight_identities"] += 1

    # Two actual scalar survivor sets in an interval have empty intersection.
    layer1 = survivors([2, 3], [(0,), (0,)], 1, 4)
    layer2 = survivors([2, 3], [(0,), (1,)], 1, 4)
    assert layer1 == [1] and layer2 == [3]
    assert not survivors([2, 3], [(0,), (0, 1)], 1, 4)
    # Signed pointwise lower bounds cannot be multiplied.
    p4 = [3, 5, 7, 11]
    roots1, roots2 = [0, 0, 1, 1], [1, 1, 0, 0]
    lower1 = 1 - sum(0 % p == a for p, a in zip(p4, roots1))
    lower2 = 1 - sum(0 % p == a for p, a in zip(p4, roots2))
    assert lower1 == lower2 == -1 and lower1 * lower2 == 1
    assert not all(0 % p not in (a, b) for p, a, b in zip(p4, roots1, roots2))

    for size in range(1, 7):
        ps = [3, 5, 7, 11, 13, 17][:size]
        mass = sum(Fraction(2 ** len(t), prod(t))
                   for r in range(size + 1) for t in combinations(ps, r))
        assert mass == prod(1 + Fraction(2, p) for p in ps)
        counts["factor_mass_identities"] += 1

    # Finite checks of the squarefree-screen dilation, not p-adic proofs.
    examples = [([0, -2, 1], 2), ([-1, 0, 1], 1), ([4, -4, 1], 2)]
    for coefficients, dilation in examples:
        def evaluate(n):
            return sum(a * n ** i for i, a in enumerate(coefficients))
        for p in [2, 3, 5, 7, 11]:
            for e in [1, 2, 3]:
                modulus = p ** e
                assert any(gcd(t, modulus) == 1 and evaluate(dilation * t) % modulus == 0
                           for t in range(modulus))
                counts["squarefree_examples"] += 1
    # Necessary local obstruction for h(t)=t^2: a squarefree t cannot yield
    # a multiple of 16. Thus the progression 16 Z avoids all such values.
    assert all((t * t) % 16 for t in range(4) if t % 4 != 0)
    # Properness at 2 is necessary; removing it kills every integer.
    assert not survivors([2], [(0, 1)], -10, 25)
    return {"status": "PASS: finite identities only", "counts": counts,
            "specified_prime_set_maxima": maxima,
            "arithmetic_shortcuts": {"scalar_survivors": [layer1, layer2],
                                      "joint_survivors": [], "signed_lower_product": 1},
            "scope": "No quartic bound, asymptotic sieve estimate, independent review, or formal certificate."}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
