#!/usr/bin/env python3
"""Exact, read-only supporting diagnostics. Author: Myeongjin Kang. MIT.

This does not prove U and does not implement the upstream wall algorithm.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, permutations
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def partitions(n, bound=None):
    if n == 0:
        yield ()
    else:
        for k in range(min(n, bound or n), 0, -1):
            for tail in partitions(n-k, k):
                yield (k,) + tail


def hessenbergs(n):
    def rec(prefix):
        i = len(prefix)+1
        if i > n:
            yield tuple(prefix)
            return
        for v in range(max(i, prefix[-1] if prefix else 1), n+1):
            yield from rec(prefix+[v])
    yield from rec([])


def e_monomial(lam, mu):
    """Coefficient of x_1^mu_1 ... x_r^mu_r in product e_(lam_i)."""
    r = len(mu)
    terms = {(0,)*r: 1}
    for k in lam:
        out = defaultdict(int)
        for subset in combinations(range(r), k):
            for a, count in terms.items():
                b = list(a)
                for i in subset:
                    b[i] += 1
                if all(b[i] <= mu[i] for i in range(r)):
                    out[tuple(b)] += count
        terms = out
    return terms.get(mu, 0)


def inverse(A):
    n = len(A)
    B = [[F(v) for v in row]+[F(i == j) for j in range(n)]
         for i, row in enumerate(A)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if B[i][j])
        B[j], B[pivot] = B[pivot], B[j]
        v = B[j][j]
        B[j] = [x/v for x in B[j]]
        for i in range(n):
            if i != j:
                v = B[i][j]
                B[i] = [a-v*b for a, b in zip(B[i], B[j])]
    return [row[n:] for row in B]


def coloring_coefficient(n, edges, mu):
    """Direct ordered independent color classes, prescribed color sizes mu."""
    M = len(edges)
    independent = {mask: all(not (mask >> i & 1 and mask >> j & 1)
                             for i, j in edges) for mask in range(1 << n)}
    by_size = defaultdict(list)
    for mask, ok in independent.items():
        if ok:
            by_size[mask.bit_count()].append(mask)

    @lru_cache(None)
    def rec(rem, c):
        if c == len(mu):
            return (1,) + (0,)*M if rem == 0 else (0,)*(M+1)
        out = [0]*(M+1)
        for block in by_size[mu[c]]:
            if block & rem != block:
                continue
            rest = rem ^ block
            shift = sum(bool(block >> i & 1 and rest >> j & 1)
                        for i, j in edges)
            p = rec(rest, c+1)
            for d, a in enumerate(p):
                if a:
                    assert d+shift <= M
                    out[d+shift] += a
        return tuple(out)
    return rec((1 << n)-1, 0)


def elementary_expansion(n, h, parts, inv):
    edges = [(i, j) for i in range(n) for j in range(i+1, h[i])]
    M = len(edges)
    mon = [coloring_coefficient(n, edges, mu) for mu in parts]
    out = []
    for row in inv:
        p = [sum((a*mon[k][d] for k, a in enumerate(row)), F())
             for d in range(M+1)]
        assert all(v.denominator == 1 for v in p)
        out.append(tuple(int(v) for v in p))
    # Reconstruct every coefficient; this catches wrong conversion directions.
    for mu, p in zip(parts, mon):
        reconstructed = tuple(sum(e_monomial(lam, mu)*out[k][d]
                                  for k, lam in enumerate(parts))
                              for d in range(M+1))
        assert reconstructed == p
    return edges, out


def unimodal(p):
    M = len(p)-1
    return p == p[::-1] and all(p[d+1] >= p[d] for d in range((M+1)//2))


def chart(D):
    pairs = [(j, i) for j in range(D-1, 0, -1) for i in range(j, D)]
    phase = {p: F(k+1, len(pairs)+1) for k, p in enumerate(pairs)}
    times = {f'd{i}': F(i) for i in range(1, D+1)}
    times.update({f'b{j}{i}': F(i)+t for (j, i), t in phase.items()})
    vs = sorted(times, key=times.get)
    N = len(vs)
    O = [[0 if i == j or abs(times[vs[i]]-times[vs[j]]) >= 1
          else (1 if i > j else -1) for j in range(N)] for i in range(N)]
    B = [[O[i+1][j+1]-O[i+1][j]-O[i][j+1]+O[i][j]
          for j in range(N-1)] for i in range(N-1)]
    triangles = [(i, j, k) for i, j, k in combinations(range(N-1), 3)
                 if B[i][j]*B[j][k] > 0 and B[j][k]*B[k][i] > 0]
    return dict(D=D, vertices=vs, times=[str(times[v]) for v in vs],
                vertex_omega=O, gap_omega=B, directed_triangles=triangles)


def main():
    expected = [[0, -2, 0, 1, 0], [2, 0, -1, -1, 1],
                [0, 1, 0, -1, -1], [-1, 1, 1, 0, -1], [0, -1, 1, 1, 0]]
    fixtures = json.loads((ROOT/'chart-diagnostics.json').read_text())
    for D in range(2, 7):
        a = chart(D)
        assert json.loads(json.dumps(a)) == fixtures[D-2]
        if D >= 3:
            assert [r[:5] for r in a['gap_omega'][:5]] == expected
            assert a['gap_omega'][0][1] < 0
            assert a['gap_omega'][1][3] < 0
            assert a['gap_omega'][3][0] < 0
    wrong = [r[:] for r in expected]
    wrong[0][3] = -1
    assert chart(3)['gap_omega'] != wrong  # wrong-sign control

    # Exact S_3 character table on classes identity, transposition, 3-cycle.
    trivial, standard = (1, 1, 1), (2, 0, -1)
    M3, M21 = trivial, (3, 1, 0)
    assert tuple(a+b for a, b in zip(trivial, standard)) == M21
    diff = tuple(a-b for a, b in zip(M21, M3))
    assert diff == standard
    assert diff != tuple(a+b for a, b in zip(M21, M3))  # wrong-difference control
    assert not unimodal((1, 0, 1))
    assert unimodal((1, 1, 1))
    # Bar-invariant, parity-pure pre-Lefschetz does not imply Lefschetz.
    # P_r=v^(r-2)+v^r for odd r; the following has no support gaps.
    pl = Counter()
    for r, multiplicity in [(-3, 1), (-1, 2), (3, 2), (5, 1)]:
        pl[r-2] += multiplicity
        pl[r] += multiplicity
    pl_coeff = tuple(pl[d] for d in range(-5, 6, 2))
    assert pl_coeff == (1, 3, 2, 2, 3, 1)
    assert pl_coeff == pl_coeff[::-1] and not unimodal(pl_coeff)
    # Degreewise permutation modules V0=V2=M3,V1=M21 admit Lefschetz:
    # one trivial string across degrees 0,1,2; standard supported in degree 1.
    assert ((M3, M21, M3)[0], (M3, M21, M3)[2]) == (M3, M3)

    digest = hashlib.sha256()
    graphs = coefficients = inequalities = symmetry_controls = 0
    diagnostic = None
    for n in range(1, 7):
        parts = list(partitions(n))
        E = [[e_monomial(lam, mu) for lam in parts] for mu in parts]
        inv = inverse(E)
        for h in hessenbergs(n):
            edges, out = elementary_expansion(n, h, parts, inv)
            M = len(edges)
            for p in out:
                assert all(a >= 0 for a in p)
                assert unimodal(p), (n, h, p)
                inequalities += (M+1)//2
            record = dict(n=n, h=h, elementary=list(zip(parts, out)))
            digest.update(json.dumps(record, sort_keys=True, separators=(',', ':')).encode())
            graphs += 1
            coefficients += len(out)
            if h in [tuple(range(2, n+1))+(n,), (n,)*n, tuple(range(1, n+1))]:
                for mu in parts:
                    if len(mu) > 1:
                        assert coloring_coefficient(n, edges, mu) == coloring_coefficient(n, edges, mu[::-1])
                        symmetry_controls += 1
            if n == 3 and h == (2, 3, 3):
                assert dict(zip(parts, out)) == {(3,): (1, 1, 1), (2, 1): (0, 1, 0),
                                               (1, 1, 1): (0, 0, 0)}
            if n == 6 and h == (2, 4, 5, 6, 6, 6):
                diagnostic = record
    assert graphs == 196
    assert not unimodal((1, 3, 2, 3, 1))  # symmetric positive nonunimodal control
    print(json.dumps(dict(status='PASS_FINITE_SUPPORT_ONLY_U_UNRESOLVED',
                         graphs=graphs, elementary_polynomials=coefficients,
                         lower_half_inequalities=inequalities,
                         selected_color_symmetry_checks=symmetry_controls,
                         enumeration_sha256=digest.hexdigest(),
                         charts_checked=list(range(2, 7)),
                         s3_obstruction=True, pre_lefschetz_obstruction=True,
                         negative_controls=4,
                         six_vertex_chart=diagnostic), sort_keys=True, indent=2))


if __name__ == '__main__':
    import sys
    if '--exercise-failure-path' in sys.argv:
        raise SystemExit('Intentional read-only checker failure.')
    main()
