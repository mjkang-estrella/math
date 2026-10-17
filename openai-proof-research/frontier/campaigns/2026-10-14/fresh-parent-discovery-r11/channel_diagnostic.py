#!/usr/bin/env python3
"""Exact finite diagnostic, not a proof of reconstruction or novelty. MIT."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import json


def rotate(x, j):
    return x[j:] + x[:j]


def deletion(x, p, forced_first=False):
    law = defaultdict(F)
    for mask in product((0, 1), repeat=len(x)):
        if forced_first and not mask[0]:
            continue
        k = sum(mask)
        law[''.join(c for c, keep in zip(x, mask) if keep)] += (
            p ** (k - int(forced_first)) * (1 - p) ** (len(x) - k)
        )
    return dict(law)


def input_rotated(x, p, forced=False):
    law = defaultdict(F)
    for j in range(len(x)):
        for t, w in deletion(rotate(x, j), p, forced).items():
            law[t] += w / len(x)
    return dict(law)


def circular(x, p):
    law = defaultdict(F)
    for t, w in deletion(x, p).items():
        if not t:
            law[t] += w
        else:
            for j in range(len(t)):
                law[rotate(t, j)] += w / len(t)
    return dict(law)


def main():
    checked = 0
    for n in range(1, 7):
        for bits in product('01', repeat=n):
            x = ''.join(bits)
            for p in (F(1, 3), F(1, 2), F(2, 3)):
                c, q = circular(x, p), input_rotated(x, p, True)
                assert sum(c.values()) == sum(q.values()) == 1
                assert sum(F(len(t), n) * w for t, w in c.items()) == p
                for t in c.keys() | q.keys():
                    assert F(len(t), n) * c.get(t, 0) / p == q.get(t, 0)
                checked += 1
    x, p = '0011', F(1, 2)
    d, c = input_rotated(x, p), circular(x, p)
    assert d['001'] == F(3, 64) and d['010'] == F(1, 32)
    assert c['001'] == c['010'] == F(1, 24)
    print(json.dumps({
        'status': 'EXACT_FINITE_DIAGNOSTIC_ONLY',
        'length_bias_cases': checked,
        'word': x, 'retention': str(p),
        'rotate_input_then_delete': {t: str(d[t]) for t in ('001', '010')},
        'delete_then_rotate_output': {t: str(c[t]) for t in ('001', '010')},
        'full_reconstruction_theorem_proved': False,
    }, indent=2))


if __name__ == '__main__':
    main()
