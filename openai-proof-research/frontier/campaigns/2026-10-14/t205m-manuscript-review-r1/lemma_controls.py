#!/usr/bin/env python3
"""Reviewer numeric controls of the all-order lemma *statements* just past the
finite starts.  Evidence only: the manuscript proves these lemmas for all
orders; this script checks that no statement is numerically false at the
first few orders where the symbolic argument alone is used.

  * Lemma 5.1 (low capacity): d = 8, 9.  For every L |- N_d with L_1 <= d-1 and
    L_1+...+L_4 <= 2d, K_{L^t, rho_d} >= d unless L is one of the four listed
    shapes; the three noncolumn listed shapes have K >= d-1.
  * Lemma 4.1 (high capacity): m = 7..10.  For every lam |- N_m with
    lam_1 <= m and C(lam) >= 2m+1, at least two nu |- N_{m-2}, outside
    E_{m-2}, satisfy lam_i >= nu_i >= lam_{i+4}.
  * Section 3 (wide): m = 9, 10.  For every non-row lam with lam_1 > m, either
    the weighted one-band sum (weight m-2 off E_{m-1}, else 1) is >= m-1, or
    lam is a rectangle.
Imports nothing from author packets.  SPDX-License-Identifier: MIT
"""
import json
import resource
import sys
from functools import lru_cache


def N(m):
    return m * (m + 1) // 2


def conj(lam):
    return tuple(sum(1 for x in lam if x > j) for j in range(lam[0])) if lam else ()


def exceptions(h):
    n = N(h)
    return {(n,), (1,) * n, (h,) + (1,) * (n - h), (h, 2) + (1,) * (n - h - 2)}


def parts_gen(n, cap, top_budget=None, depth=0):
    """Partitions of n with parts <= cap; optional bound on sum of first four parts."""
    if n == 0:
        yield ()
        return
    for first in range(min(n, cap), 0, -1):
        if top_budget is not None and depth < 4 and first > top_budget:
            continue
        nb = None if top_budget is None else (top_budget - first if depth < 4 else None)
        for rest in parts_gen(n - first, first, nb, depth + 1):
            yield (first,) + rest


def strips_below(lam, k):
    L = len(lam)
    out = []

    def rec(i, left, cur):
        if i == L:
            if left == 0:
                out.append(tuple(x for x in cur if x))
            return
        lo = lam[i + 1] if i + 1 < L else 0
        for x in range(lam[i], lo - 1, -1):
            if lam[i] - x > left:
                break
            rec(i + 1, left - (lam[i] - x), cur + [x])
    rec(0, k, [])
    return out


@lru_cache(None)
def kostka(lam, mu):
    if not mu:
        return 1 if not lam else 0
    if sum(lam) != sum(mu) or len(lam) > len(mu):
        return 0
    return sum(kostka(k, mu[:-1]) for k in strips_below(lam, mu[-1]))


def four_strip_predecessors(lam, n):
    L = len(lam)
    out = []

    def rec(i, left, cur):
        if i == L:
            if left == 0:
                out.append(tuple(x for x in cur if x))
            return
        lo = lam[i + 4] if i + 4 < L else 0
        hi = min(lam[i], cur[-1] if cur else lam[i], left)
        for x in range(hi, lo - 1, -1):
            rec(i + 1, left - x, cur + [x])
    rec(0, n, [])
    return out


def low_lemma(d):
    n = N(d)
    rho = tuple(range(d, 0, -1))
    listed = {(1,) * n, (2,) + (1,) * (n - 2), (d - 1,) + (1,) * (n - d + 1),
              (d - 1, d - 1) + (1,) * (n - 2 * d + 2)}
    count, bad, listed_vals, minimum = 0, [], {}, None
    for L in parts_gen(n, d - 1, 2 * d):
        count += 1
        K = kostka(conj(L), rho)
        if L in listed:
            listed_vals[str(L[:3]) + '...len%d' % len(L)] = K
            continue
        minimum = K if minimum is None else min(minimum, K)
        if K < d:
            bad.append(L)
    kostka.cache_clear()
    ok = not bad and all(v >= d - 1 for k, v in listed_vals.items() if not k.startswith('(1, 1, 1)'))
    return {'d': d, 'shapes': count, 'min_K_unlisted': minimum, 'listed_K': listed_vals,
            'violations': [list(b) for b in bad[:5]], 'pass': ok}


def high_lemma(m):
    n, h = N(m), m - 2
    E = exceptions(h)
    count, bad, min_usable = 0, [], None
    for lam in parts_gen(n, m):
        if sum(lam[:4]) < 2 * m + 1:
            continue
        count += 1
        usable = sum(1 for nu in four_strip_predecessors(lam, N(h)) if nu not in E)
        min_usable = usable if min_usable is None else min(min_usable, usable)
        if usable < 2:
            bad.append(lam)
    return {'m': m, 'shapes': count, 'min_usable_predecessors': min_usable,
            'violations': [list(b) for b in bad[:5]], 'pass': not bad and count > 0}


def wide_case(m):
    n, h = N(m), m - 1
    E = exceptions(h)
    count, rect, bad, minimum = 0, 0, [], None
    for first in range(m + 1, n):
        for rest in parts_gen(n - first, first):
            lam = (first,) + rest
            count += 1
            if len(set(lam)) == 1:
                rect += 1
                continue
            one = sum((m - 2) if nu not in E else 1 for nu in strips_below(lam, m))
            minimum = one if minimum is None else min(minimum, one)
            if one < m - 1:
                bad.append(lam)
    return {'m': m, 'nonrow_wide_shapes': count, 'rectangles': rect,
            'min_weighted_one_band': minimum, 'violations': [list(b) for b in bad[:5]],
            'pass': not bad}


def main():
    report = {'evidence_only': True,
              'low_lemma': [low_lemma(d) for d in (8, 9)],
              'high_lemma': [high_lemma(m) for m in (7, 8, 9, 10)],
              'wide_case': [wide_case(m) for m in (9, 10)]}
    ok = all(r['pass'] for k in ('low_lemma', 'high_lemma', 'wide_case') for r in report[k])
    report['result'] = 'PASS_LEMMA_STATEMENT_CONTROLS' if ok else 'FAIL_LEMMA_STATEMENT_CONTROLS'
    print(json.dumps(report, indent=1, sort_keys=True))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    resource.setrlimit(resource.RLIMIT_AS, (4 << 30, 4 << 30))
    sys.setrecursionlimit(10000)
    main()
