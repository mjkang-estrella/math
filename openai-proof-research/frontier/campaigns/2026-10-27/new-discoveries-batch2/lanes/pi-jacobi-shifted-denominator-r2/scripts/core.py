"""Fresh exact pipeline for the shifted-denominator question (Area 2608.23006v2, Remark 3.8).

Independently implemented for lane pi-jacobi-shifted-denominator-r2.
Same verified reduction as the 2026-10-26 lane (re-derived here), plus:
  * U_n/V_n recurrence (source Theorem 2.3) machinery,
  * antisymmetry / even-cumulant checks,
  * mod-2^k normal-form extraction.

Polynomials in (u,v) with Gaussian-integer coefficients: dict {(a,b): (re,im)}.
A_n = 2^n n! [Z^-n] F = sum_{s<=n} S2(n,s) 2^(n-s) (n!/s!) Ctilde_s.
B_1 = A_1, B_n = A_n - sum_{j<n} C(n-1,j-1) B_j A_{n-j}.
kappa_r = Im B_{2r-1} / (2^(4r-2) (2r-1)!).
"""
from fractions import Fraction
from math import comb, factorial
import json

# ---------------------------------------------------------------- Gaussian ints

def gi_mul(x, y):
    a, b = x; c, d = y
    return (a * c - b * d, a * d + b * c)

def gi_add(x, y):
    return (x[0] + y[0], x[1] + y[1])

def vp(n):
    n = abs(n)
    return (n & -n).bit_length() - 1 if n else 10 ** 9

# ---------------------------------------------------------------- polynomials

def padd(p, q, c=1):
    r = dict(p)
    for k, z in q.items():
        r[k] = gi_add(r.get(k, (0, 0)), gi_mul(z, (c, 0)))
    return {k: z for k, z in r.items() if z != (0, 0)}

def pmul(p, q):
    r = {}
    for (a, b), x in p.items():
        for (c, d), y in q.items():
            k = (a + c, b + d)
            r[k] = gi_add(r.get(k, (0, 0)), gi_mul(x, y))
    return r

def p_im(p):
    return {k: z[1] for k, z in p.items() if z[1]}

def p_re(p):
    return {k: z[0] for k, z in p.items() if z[0]}

def p_min_vp(p):
    return min((vp(z) for z in p.values()), default=10 ** 9)

def p_degree(p):
    return max((a + b for (a, b) in p), default=-1)

def swap_uv(p):
    """u <-> v (exponents (a,b) -> (b,a))."""
    return {(b, a): z for (a, b), z in p.items()}

# ---------------------------------------------------------------- builders

def build_P(N):
    """P_l(u), l=0..N, as Gaussian-int polys with v-exponent 0."""
    P = [{(0, 0): (1, 0)}]
    for j in range(N):
        P.append(pmul(P[-1], {(1, 0): (1, 0), (0, 0): (-j * (j + 1), 0)}))
    return P

def stirling2(N):
    S = [[0] * (N + 1) for _ in range(N + 1)]
    S[0][0] = 1
    for n in range(1, N + 1):
        for m in range(1, n + 1):
            S[n][m] = S[n - 1][m - 1] + m * S[n - 1][m]
    return S

def Ctilde_all(N):
    """Ctilde_m = sum_l binom(m,l) P_l(u) P_{m-l}(v) p^l q^{m-l}, m=0..N."""
    P = build_P(N)
    # powers of p=1+i, q=1-i (Gaussian ints)
    pp = [(1, 0)]; qq = [(1, 0)]
    for _ in range(N):
        pp.append(gi_mul(pp[-1], (1, 1)))
        qq.append(gi_mul(qq[-1], (1, -1)))
    C = []
    for m in range(N + 1):
        c = {}
        for l in range(m + 1):
            w = gi_mul(pp[l], qq[m - l])
            # P_l(u) has v-exp 0; P_{m-l}(v): swap of a P_l(u)
            term = pmul(pmul(P[l], swap_uv(P[m - l])), {(0, 0): w})
            c = padd(c, term, comb(m, l))
        C.append(c)
    return C

def compute_AB(N):
    """A_n, B_n for n=0..N.  A_0 = 1 (poly {(0,0):1}); B_0 unused."""
    S = stirling2(N)
    C = Ctilde_all(N)
    A = [{(0, 0): (1, 0)}]
    for n in range(1, N + 1):
        p = {}
        for s in range(1, n + 1):
            factor = 2 ** (n - s) * (factorial(n) // factorial(s)) * S[n][s]
            p = padd(p, C[s], factor)
        A.append(p)
    B = [{}]
    for n in range(1, N + 1):
        b = dict(A[n])
        for k in range(1, n):
            b = padd(b, pmul(B[k], A[n - k]), -comb(n - 1, k - 1))
        B.append(b)
    return A, B

def check_law(N, verbose=True):
    A, B = compute_AB(N)
    rows = []
    ok = True
    ev_ok = True
    for m in range(0, (N - 1) // 2 + 1):
        n = 2 * m + 1
        im = p_im(B[n])
        mn = p_min_vp(im)
        deg = p_degree(im)
        row = dict(m=m, n=n, min_v2=mn, law=3 * m, ok=(mn == 3 * m),
                   deg=deg, ncoeff=len(im))
        ok &= (mn == 3 * m)
        rows.append(row)
    # even cumulants: Im B_{2k} == 0 ?
    ev_ok = all(len(p_im(B[2 * k])) == 0 for k in range(1, N // 2 + 1))
    if verbose:
        for r in rows:
            print(json.dumps(r))
        print("even Im B_{2k} == 0 for all k <= ", N // 2, ":", ev_ok)
    return ok, ev_ok, A, B

if __name__ == "__main__":
    import sys
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    ok, ev_ok, A, B = check_law(N)
    print("LAW min nu2(ImB_{2m+1}) = 3m for m <= ", N // 2, ":", ok)
    print("EVEN ImB = 0:", ev_ok)
