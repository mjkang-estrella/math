#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Read-only exact supporting checks. No source code imports or graph census."""
from collections import defaultdict
from itertools import product
from math import comb
import hashlib
import json


def add(a, b, scale=1):
    out = defaultdict(int, a)
    for e, c in b.items():
        out[e] += scale*c
    return {e: c for e, c in out.items() if c}


def mul(a, b):
    out = defaultdict(int)
    for e, c in a.items():
        for f, d in b.items():
            key = tuple(x+y for x, y in zip(e, f)) if isinstance(e, tuple) else e+f
            out[key] += c*d
    return {e: c for e, c in out.items() if c}


def gauss(n, j):
    if j < 0 or j > n:
        return {}
    row = [{0: 1}]
    for a in range(1, n+1):
        nxt = []
        for b in range(a+1):
            left = row[b] if b < len(row) else {}
            right = row[b-1] if b else {}
            shifted = {e+a-b: c for e, c in right.items()}
            nxt.append(add(left, shifted))
        row = nxt
    return row[j]


def dilog_bar_control(n, wrong=False):
    # Common denominator prod_{i=1}^n (1-v^(-2i)).
    # d_j(v)=v^(-j*j)/D_j; d_k(v^-1)=(-1)^k v^(-k)/D_k.
    out = {}
    for j in range(n+1):
        k = n-j
        shift = -j*j-(k*k if wrong else k)
        term = {shift-2*e: (-1)**k*c for e, c in gauss(n, j).items()}
        out = add(out, term)
    return out


def elementary_weights(a, j):
    row = [{0: 1}]+[{} for _ in range(j)]
    for e in range(1-a, a, 2):
        for k in range(j, 0, -1):
            row[k] = add(row[k], {f+e: c for f, c in row[k-1].items()})
    return row[j]


def strings(poly):
    if not poly:
        return {}
    if any(poly.get(-e, 0) != c for e, c in poly.items()):
        raise ValueError('not centered')
    bound = max(poly)
    parity = bound % 2
    if any(e % 2 != parity for e in poly):
        raise ValueError('not parity pure')
    previous = 0
    result = {}
    for e in range(-bound, 1, 2):
        diff = poly.get(e, 0)-previous
        if diff:
            result[1-e] = diff
        previous = poly.get(e, 0)
    return result


def reconstruct(parts):
    out = {}
    for length, multiplicity in parts.items():
        out = add(out, {e: multiplicity for e in range(1-length, length, 2)})
    return out


def omega(a, b):
    matrix = ((0, -1, 0), (1, 0, -1), (0, 1, 0))
    return sum(a[i]*matrix[i][j]*b[j] for i in range(3) for j in range(3))


def quadratic(a):
    return (a[0]*a[1]+a[1]*a[2]) % 2


def eval_one(poly):
    return sum(poly.values())


def main():
    for n in range(10):
        assert dilog_bar_control(n) == ({0: 1} if n == 0 else {})
    assert dilog_bar_control(2, wrong=True)  # wrong inverse numerator detected

    simple_count = 0
    for a in range(1, 11):
        for j in range(a+1):
            p = elementary_weights(a, j)
            assert sum(p.values()) == comb(a, j)
            assert all(e % 2 == j*(a-j) % 2 for e in p)
            decomposition = strings(p)
            assert all(c >= 0 for c in decomposition.values())
            assert reconstruct(decomposition) == p
            simple_count += 1
    # This retained obstruction tests the unpaid distinction, not U.
    nonlefschetz = {-2: 1, 2: 1}
    assert strings(nonlefschetz) == {3: 1, 1: -1}
    assert reconstruct(strings(nonlefschetz)) == nonlefschetz

    vectors = list(product(range(-1, 2), repeat=3))
    for a in vectors:
        for b in vectors:
            total = tuple(x+y for x, y in zip(a, b))
            assert quadratic(total) == (quadratic(a)+quadratic(b)+omega(a, b)) % 2
    assert quadratic((-1, 1, 0)) == quadratic((0, -1, 1)) == 1

    one = {(0, 0): 1}
    x = {(1, 0): 1}
    y = {(0, 1): 1}
    A, B, C = {(1, -1): 1}, {(-1, -1): 1}, {(-1, 1): 1}
    z = add(add(A, B), C)
    assert mul(A, C) == one
    assert mul(z, {(1, 1): 1}) == add(add(mul(x, x), mul(y, y)), one)
    forward = [x, y]
    for _ in range(9):
        nxt = add(mul(z, forward[-1]), forward[-2], -1)
        assert mul(forward[-2], nxt) == add(mul(forward[-1], forward[-1]), one)
        forward.append(nxt)
    backward = [y, x]
    for _ in range(9):
        nxt = add(mul(z, backward[-1]), backward[-2], -1)
        assert mul(backward[-2], nxt) == add(mul(backward[-1], backward[-1]), one)
        backward.append(nxt)
    values = [eval_one(p) for p in forward]
    assert values == [eval_one(p) for p in backward]
    assert values[:5] == [1, 1, 2, 5, 13]
    assert all(a < b for a, b in zip(values[2:], values[3:]))
    assert eval_one(z) == 3
    wrong_z = add(A, C)
    wrong_next = add(mul(wrong_z, y), x, -1)
    assert mul(x, wrong_next) != add(mul(y, y), one)
    # Coefficient specializations merge monomials: AC=1; do not transfer X_u.
    assert mul(A, C) == one and A != one and C != one

    payload = {
        'scope': 'Exact supporting arithmetic only; full U UNRESOLVED',
        'dilog_inverse_identities': 10,
        'simple_jump_polynomials': simple_count,
        'quadratic_refinement_pairs': len(vectors)**2,
        'rank_two_exchange_checks': 18,
        'rank_two_evaluations': values,
        'negative_controls': ['wrong dilog inverse numerator', 'non-Lefschetz centered polynomial', 'missing regular-function term'],
        'limits': 'No actual cyclic-chart jump computation, source witness implementation, full-U census, or independent proof/contribution review.',
    }
    data = json.dumps(payload, sort_keys=True, separators=(',', ':')).encode()
    payload['aggregate_sha256'] = hashlib.sha256(data).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
