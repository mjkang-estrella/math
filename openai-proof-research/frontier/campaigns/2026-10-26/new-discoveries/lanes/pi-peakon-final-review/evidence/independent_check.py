#!/usr/bin/env python3
"""pi-peakon-final-review independent exact check (own algorithm, Fraction arithmetic).

Checks, over Q with random rational data:
  A. det(I - tL) == 1 - Lambda*H(t) as polynomials (evaluated at N+1 integer points),
     for random u,v,z,gamma; includes ties (proportional u,v entries), N=0, N=1,
     degenerate curve points (lam=0, xi=+-1) not reachable by the z-parametrization.
  B. tr(L^m) == sum over PARTITIONS of m of m*(j-1)!/(prod k_i * prod r_s!) * Lam^j * prod h^(k)
     for m = 1..M, including m > N (h^(k)=0 for k>N tested implicitly).
  C. The two printed source families: a_m(1..1)=1, a_{j+1}(m-j,1..1)=m/(m-j), a_1(m)=1.
No use of the candidate's check_peakon_coefficients.py or review-check.py.
"""
from fractions import Fraction as F
from math import prod
from itertools import product
import random

random.seed(20261027)

def mat_mul(A, B):
    if not A or not B:
        return []
    n, k, m = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(m)] for i in range(n)]

def det(M):
    n = len(M)
    if n == 0:
        return F(1)
    M = [row[:] for row in M]
    sign, d = F(1), F(1)
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(M[r][c]))
        if M[p][c] == 0:
            return F(0)
        if p != c:
            M[c], M[p] = M[p], M[c]; sign = -sign
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            for cc in range(c, n):
                M[r][cc] -= f * M[c][cc]
    return sign * d

def build(u, v, lam, xi, gamma):
    n = len(u)
    B = [[(u[i]*v[j] - v[i]*u[j] if i < j else F(0)) for j in range(n)] for i in range(n)]
    A = [[(u[i]*v[j] - v[i]*u[j]) / 2 for j in range(n)] for i in range(n)]
    T = [[(u[i]*v[j] + v[i]*u[j]) / 2 for j in range(n)] for i in range(n)]
    S = [[B[i][j] - A[i][j] for j in range(n)] for i in range(n)]
    L = [[S[i][j] + lam*T[i][j] + xi*A[i][j] for j in range(n)] for i in range(n)]
    D = [[(gamma / 2) * a + t for a, t in zip(A[i], T[i])] for i in range(n)]
    return B, L, D

def hamiltonians(B, D, N):
    h = []
    P = [[F(1 if i == j else 0) for j in range(len(B))] for i in range(len(B))]
    for k in range(1, N + 1):
        h.append(F(k) * sum(D[i][j] * P[j][i] for j in range(len(B)) for i in range(len(B))))
        P = mat_mul(P, B)
    return h

def H_poly(B, D, N):
    # H(t) = sum_{k=1}^{N} tr(D B^{k-1}) t^k ; coefficient list index k
    h1 = []
    P = [[F(1 if i == j else 0) for j in range(len(B))] for i in range(len(B))]
    for k in range(0, N):
        h1.append(sum(D[i][j] * P[j][i] for j in range(len(B)) for i in range(len(B))))
        P = mat_mul(P, B)
    return [F(0)] + h1  # coeff[k] = tr(D B^{k-1}), H = sum coeff[k] t^k

def check_case(N, tied, mmax, tag):
    if N == 0:
        u, v = [], []
    else:
        u = [F(random.randint(-6, 6), random.randint(1, 7)) for _ in range(N)]
        v = [F(random.randint(-6, 6), random.randint(1, 7)) for _ in range(N)]
        if tied and N >= 2:
            v[1] = v[0] * (u[1] / u[0]) if u[0] != 0 else v[0]  # force u1 v2 = v1 u2
    z = F(random.randint(-9, 9), random.randint(1, 5))
    gamma = F(random.randint(-7, 7), random.randint(1, 4))
    while 2 * z + gamma == 0:
        gamma = F(random.randint(-7, 7), random.randint(1, 4))
    assert 2 * z + gamma != 0
    lam = (z*z - 1) / (2*z + gamma)
    xi = (z*z + gamma*z + 1) / (2*z + gamma)
    assert xi*xi == lam*lam + gamma*lam + 1
    B, L, D = build(u, v, lam, xi, gamma)

    # A: determinant collapse at N+1 evaluation points (both sides poly deg <= N)
    pts = list(range(-(N + 1), 1)) if N > 0 else [0]
    Hc = H_poly(B, D, N)
    for s in pts:
        I_tL = [[(F(1) if i == j else F(0)) - s * L[i][j] for j in range(N)] for i in range(N)]
        lhs = det(I_tL)
        rhs = F(1) - lam * sum(Hc[k] * s**k for k in range(len(Hc)))
        assert lhs == rhs, f"DET FAIL {tag} N={N} s={s}: {lhs} != {rhs}"

    # A2: degenerate curve points lam=0, xi=1 and xi=-1 (gamma arbitrary, z-param unreachable)
    for lam0, xi0 in [(F(0), F(1)), (F(0), F(-1))]:
        _, L0, _ = build(u, v, lam0, xi0, gamma)
        for s in pts:
            I_tL = [[(F(1) if i == j else F(0)) - s * L0[i][j] for j in range(N)] for i in range(N)]
            assert det(I_tL) == F(1), f"DEG FAIL {tag} N={N} xi={xi0} s={s}"

    # B: full universal partition identity for all m in 1..mmax
    h = hamiltonians(B, D, N)
    def partitions(m, cap):
        # partitions of m with all parts <= cap, as (sorted desc tuple)
        res = []
        def rec(rem, mx, cur):
            if rem == 0:
                res.append(tuple(cur)); return
            for k in range(min(rem, mx), 0, -1):
                rec(rem - k, k, cur + [k])
        rec(m, cap if cap else m, [])
        return res
    for m in range(1, mmax + 1):
        lhs = sum(L[i][i] for i in range(N))
        P = L
        for _ in range(m - 1):
            P = mat_mul(P, L)
        lhs = sum(P[i][i] for i in range(N))
        rhs = F(0)
        for part in partitions(m, m):
            j = len(part)
            rs = {}
            for k in part:
                rs[k] = rs.get(k, 0) + 1
            mult = 1
            for k, c in rs.items():
                mult *= factorial(c)
            a = F(m) * factorial(j - 1) / (prod(part) * mult)
            hp = F(1)
            for k in part:
                hp *= h[k - 1] if k - 1 < len(h) else F(0)
            rhs += a * (lam ** j) * hp
        assert lhs == rhs, f"TRACE FAIL {tag} N={N} m={m}: {lhs} != {rhs}"
    return True

def factorial(x):
    r = 1
    for i in range(2, x + 1):
        r *= i
    return r

# C: printed coefficient families (pure arithmetic)
for m in range(1, 13):
    assert F(m) * factorial(m - 1) / (prod([1]*m) * factorial(m)) == 1  # a_m(1..1)=1
    assert F(m) * factorial(0) / (m * 1) == 1  # a_1(m) = 1
    for j in range(0, m - 1):
        part = [m - j] + [1] * j
        rs = {}
        for k in part: rs[k] = rs.get(k, 0) + 1
        mult = 1
        for k, c in rs.items(): mult *= factorial(c)
        a = F(m) * factorial(j) / (prod(part) * mult)
        assert a == F(m) / (m - j), f"FAMILY FAIL m={m} j={j}: {a}"

cnt = 0
for trial in range(30):
    for N in [0, 1, 2, 3, 4, 5, 6]:
        check_case(N, tied=(trial % 3 == 0), mmax=9, tag=f"t{trial}")
        cnt += 1
print(f"PASS: {cnt} cases, det collapse + degenerate curve + universal partition identity "
      f"(m<=9, incl m>N), ties, N=0/1, printed families m<=12. All exact over Q.")
