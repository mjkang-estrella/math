#!/usr/bin/env python3
"""Exhaustive small-order controls (not proofs).

For alphabet mu_4 = {1,i,-1,-i} (letters 0..3, value i^k) or mu_3 =
{1,w,w^2} (letters 0..2, value w^k), enumerate every first row with first
letter 0 (multiplying a row by a unit preserves the Hadamard property) and
count circulant complex Hadamard rows: all nontrivial periodic
autocorrelations sum_j h_j conj(h_{j+t}) vanish.  Letters are exponents, so
h_j conj(h_k) = zeta^(a_j - a_k), and an autocorrelation is zero iff the
multiset of exponent differences is a vanishing sum of q-th roots of unity:
for q = 4 iff counts c0 = c2 and c1 = c3; for q = 3 iff c0 = c1 = c2.
A cheap row-sum filter |sum h_j|^2 = n is applied first.
Usage: search_small.py q n [n ...]
"""
import itertools, json, sys

def row_sum_norm(row, q):
    if q == 4:
        c = [0] * 4
        for a in row: c[a] += 1
        re, im = c[0] - c[2], c[1] - c[3]
        return re * re + im * im
    c = [0] * 3
    for a in row: c[a] += 1
    # |c0 + c1 w + c2 w^2|^2 = c0^2 + c1^2 + c2^2 - c0 c1 - c1 c2 - c2 c0
    return c[0]**2 + c[1]**2 + c[2]**2 - c[0]*c[1] - c[1]*c[2] - c[2]*c[0]

def perfect(row, q):
    n = len(row)
    for t in range(1, n // 2 + 1):
        c = [0] * q
        for j in range(n):
            c[(row[j] - row[(j + t) % n]) % q] += 1
        if q == 4:
            if c[0] != c[2] or c[1] != c[3]: return False
        else:
            if not (c[0] == c[1] == c[2]): return False
    return True

out = {}
q = int(sys.argv[1])
for n in map(int, sys.argv[2:]):
    total = good = 0; example = None
    for tail in itertools.product(range(q), repeat=n - 1):
        row = (0,) + tail
        total += 1
        if row_sum_norm(row, q) != n: continue
        if perfect(row, q):
            good += 1
            if example is None: example = list(row)
    out[str(n)] = {"rows_enumerated": total, "perfect_rows_with_first_letter_0": good,
                   "example_exponents": example}
    print(json.dumps({"q": q, "n": n, **out[str(n)]}), flush=True)
