#!/usr/bin/env python3
"""Exact finite checks of author calculations; not reconstruction evidence.
Copyright 2026 Myeongjin Kang. MIT license. No affiliation asserted.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
import importlib.util
import json
from pathlib import Path


def load_prior():
    p = Path(__file__).parent / 'private/prior-r11/channel_diagnostic.py'
    spec = importlib.util.spec_from_file_location('prior_channel', p)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def cyclic_feature(x, zs):
    """G_{k,z}=n^{-k} sum of rooted cyclic tuples, including closing gap."""
    n, k = len(x), len(zs)
    result = F(0)
    for r in range(n):
        for tail in combinations(range(1, n), k - 1):
            offsets = (0,) + tail
            if all(x[(r + j) % n] for j in offsets):
                gaps = tuple(offsets[j + 1] - offsets[j] for j in range(k - 1))
                gaps += (n - offsets[-1],)
                weight = F(1)
                for z, g in zip(zs, gaps):
                    weight *= z ** g
                result += weight
    return result / n ** k


def interleavings(zlists):
    sizes = [len(z) for z in zlists]
    total = sum(sizes)
    for v in range(1, total + 1):
        for ranks in product(range(v), repeat=total - 1):
            ranks = (0,) + ranks  # first factor root is merged root
            if set(ranks) != set(range(v)):
                continue
            znew = [F(1)] * v
            start = 0
            valid = True
            for zs, k in zip(zlists, sizes):
                rr = ranks[start:start + k]
                start += k
                distances = [(a - rr[0]) % v for a in rr]
                if len(set(rr)) != k or distances != sorted(distances):
                    valid = False
                    break
                for j, z in enumerate(zs):
                    a, b = rr[j], rr[(j + 1) % k]
                    steps = (b - a) % v if k > 1 else v
                    for h in range(steps):
                        znew[(a + h) % v] *= z
            if valid:
                yield v, tuple(znew)


def isolate(orbit):
    remaining = list(orbit)
    literals = []
    while len(remaining) > 1:
        i = next(i for i in range(len(remaining[0]))
                 if len({x[i] for x in remaining}) == 2)
        groups = [[x for x in remaining if x[i] == bit] for bit in (0, 1)]
        bit = min(range(2), key=lambda b: len(groups[b]))
        remaining = groups[bit]
        literals.append((i, bit))
    return remaining[0], literals


def main():
    prior = load_prior()
    conversions = isolations = 0
    for n in range(1, 7):
        for bits in product('01', repeat=n):
            x = ''.join(bits)
            for p in (F(1, 3), F(1, 2), F(2, 3)):
                c = prior.circular(x, p)
                converted = defaultdict(F)
                for t, w in c.items():
                    if t:
                        accepted = w * F(len(t), n) / p
                        converted[t] += accepted * p
                        converted[t[1:]] += accepted * (1 - p)
                expected = prior.input_rotated(x, p)
                assert all(converted[t] == expected.get(t, 0)
                           for t in converted.keys() | expected.keys())
                conversions += 1
            xb = tuple(int(v) for v in x)
            orbit = {xb[j:] + xb[:j] for j in range(n)}
            y, literals = isolate(orbit)
            assert len(literals) <= len(orbit).bit_length() - 1
            assert sum(all(z[i] == b for i, b in literals) for z in orbit) == 1
            # Every rotation of the cylinder still isolates exactly one point.
            for r in range(n):
                assert sum(all(z[(i + r) % n] == b for i, b in literals)
                           for z in orbit) == 1
            isolations += 1

    parameter_lists = [
        ((F(1, 2), F(2, 3)), (F(3, 4), F(4, 5))),
        ((F(1, 2),), (F(2, 3), F(3, 4))),
        ((F(1), F(1, 3)), (F(1, 2), F(1), F(2, 3))),
    ]
    closures = 0
    for zlists in parameter_lists:
        terms = list(interleavings(zlists))
        total = sum(map(len, zlists))
        for n in (3, 4, 5):
            for x in product((0, 1), repeat=n):
                left = F(1)
                for zs in zlists:
                    left *= cyclic_feature(x, zs)
                right = sum((F(n) ** (v - total)) * cyclic_feature(x, zs)
                            for v, zs in terms if v <= n)
                assert left == right, (x, zlists, left, right)
                closures += 1

    n = 12
    a, b = {0, 1, 4, 6}, {0, 1, 3, 7}
    assert all({(v + r) % n for v in a} != b for r in range(n))
    autocorr = lambda s: [sum((v + d) % n in s for v in s) for d in range(n)]
    assert autocorr(a) == autocorr(b)
    parseval_examples = []
    for m in range(1, 9):
        nn = 12 * m
        xx, yy = {0, 3 * m, 7 * m}, {0, 2 * m, 7 * m}
        assert all({(v + r) % nn for v in xx} != yy for r in range(nn))
        coeffs = [F(sum((j + d) % nn in xx for j in xx)
                    - sum((j + d) % nn in yy for j in yy), nn)
                  for d in range(nn)]
        expected = {a * m: F(b, nn) for a, b in
                    [(2, -1), (3, 1), (4, 1), (5, -1),
                     (7, -1), (8, 1), (9, 1), (10, -1)]}
        assert all(c == expected.get(d, 0) for d, c in enumerate(coeffs))
        assert next(d for d, c in enumerate(coeffs) if c) == 2 * m
        assert sum(abs(c) for c in coeffs) == F(8, nn)
        assert sum(c * c for c in coeffs) == F(8, nn * nn)
        parseval_examples.append({'m': m, 'n': nn, 'first_gap': 2 * m,
                                  'coefficient_l1': str(F(8, nn))})
    print(json.dumps({
        'status': 'EXACT_FINITE_DIAGNOSTIC_ONLY',
        'C_to_P_cases': conversions,
        'orbit_isolator_cases': isolations,
        'cyclic_gap_product_cases': closures,
        'homometric_sets': [sorted(a), sorted(b)],
        'common_autocorrelation': autocorr(a),
        'parseval_constant_scale_examples': parseval_examples,
        'quasipolynomial_circular_reconstruction_proved': False,
    }, indent=2))


if __name__ == '__main__':
    main()
