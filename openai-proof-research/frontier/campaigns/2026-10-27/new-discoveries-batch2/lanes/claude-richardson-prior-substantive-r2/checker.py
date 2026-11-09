"""Independent exact checker for the Christoffel-Darboux (CD) bridge objection.

Finite error-detection only; the universal argument is in review.md.
Checks, for 1<=n<=NMAX, 1<=r<=RMAX, with exact integers/Fractions only:
 (a) Berg 2006/2011 Sec.4 displayed entry formula equals the exact inverse of
     the matrix (1/(r*C(r+i+j,r)))_{0<=i,j<n}  [i.e. r*R^{-1}, R_ij=1/C(i+j+r,r)];
 (b) CD identity on coefficient arrays:
     (2n+r-1) * (-1)^(i+j) N[i,j] = -n(n+r-1) * D[i,j],
     D(x,y) = (Q_n(x)Q_{n-1}(y) - Q_{n-1}(x)Q_n(y))/(x-y) in Z[x,y];
 (c) gcd(n(n-1), 2n-1) = 1;
 (d) R^{-1} integral  <=>  r | n(n-1)   (Richardson Conjecture 5.1);
 (e) exact common denominator lcm(den R^{-1}) = r/gcd(r, n(n-1)) (law observed unproved in r1).
"""
import json, sys, datetime
from fractions import Fraction
from math import comb, gcd, lcm

NMAX, RMAX = int(sys.argv[1]), int(sys.argv[2])

def C(a, b):
    return comb(a, b) if 0 <= b <= a else 0

def P(i, k, r):
    return C(k, i) * C(k + r + i - 1, i)

def Q(k, r):  # integer coefficient list of Q_k(x) = sum (-1)^i P_i(k) x^i
    return [(-1) ** i * P(i, k, r) for i in range(k + 1)]

def inverse(M):
    n = len(M); A = [row[:] + [Fraction(int(i == j)) for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        p = next(i for i in range(c, n) if A[i][c] != 0); A[c], A[p] = A[p], A[c]
        piv = A[c][c]; A[c] = [v / piv for v in A[c]]
        for i in range(n):
            if i != c and A[i][c] != 0:
                f = A[i][c]; A[i] = [a - f * b for a, b in zip(A[i], A[c])]
    return [row[n:] for row in A]

def divided_difference(a, b, n):  # coefficients of (a(x)b(y)-b(x)a(y))/(x-y), size n x n
    D = [[0] * n for _ in range(n)]
    for s, as_ in enumerate(a):
        for t, bt in enumerate(b):
            c = as_ * bt
            if c == 0 or s == t:
                continue
            # (x^s y^t - x^t y^s)/(x-y)
            lo, hi, sign = (t, s, 1) if s > t else (s, t, -1)
            for u in range(hi - lo):  # x^lo y^lo * sum_{u} x^(hi-lo-1-u) y^u
                D[lo + hi - lo - 1 - u][lo + u] += sign * c
    return D

counts = {'berg_formula_entries': 0, 'cd_entries': 0, 'gcd_cases': 0, 'iff_cases': 0, 'integral_cases': 0, 'denominator_law_cases': 0}
for n in range(1, NMAX + 1):
    assert gcd(n * (n - 1), 2 * n - 1) == 1; counts['gcd_cases'] += 1
    for r in range(1, RMAX + 1):
        R = [[Fraction(1, C(i + j + r, r)) for j in range(n)] for i in range(n)]
        Rinv = inverse(R)
        N = [[sum((2 * k + r) * P(i, k, r) * P(j, k, r) for k in range(n)) for j in range(n)] for i in range(n)]
        for i in range(n):
            for j in range(n):
                berg = (-1) ** (i + j) * sum((r + 2 * k) * C(k, i) * C(k, j) * C(r + k + i - 1, i) * C(r + k + j - 1, j)
                                             for k in range(max(i, j), n))
                assert Fraction(berg) == r * Rinv[i][j]; counts['berg_formula_entries'] += 1
        D = divided_difference(Q(n, r), Q(n - 1, r), n)
        for i in range(n):
            for j in range(n):
                assert (2 * n + r - 1) * (-1) ** (i + j) * N[i][j] == -n * (n + r - 1) * D[i][j]
                counts['cd_entries'] += 1
        integral = all(v.denominator == 1 for row in Rinv for v in row)
        assert integral == (n * (n - 1) % r == 0); counts['iff_cases'] += 1
        counts['integral_cases'] += integral
        den = 1
        for row in Rinv:
            for v in row:
                den = lcm(den, v.denominator)
        assert den == r // gcd(r, n * (n - 1)); counts['denominator_law_cases'] += 1
print(json.dumps({'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'NMAX': NMAX, 'RMAX': RMAX,
                  'all_passed': True, 'counts': counts}))
