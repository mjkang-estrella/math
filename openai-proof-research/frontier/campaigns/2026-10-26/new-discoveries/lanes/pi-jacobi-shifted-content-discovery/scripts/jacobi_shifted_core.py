"""Independent exact computation of the formal phase constants (Area, Definition 2.1).

Pipeline (all exact, Gaussian-integer / rational arithmetic):

  F(Z) = sum_{c,d>=0} P_c(u) P_d(v) (p/2)^c (q/2)^d /(c! d!) * 1/((Z-1)...(Z-c-d))
         with u = mu_alpha = A - 1/4, v = mu_beta = B - 1/4, p = 1+i, q = 1-i,
         P_l(w) = prod_{j=0}^{l-1} (w - j(j+1)).

  [Z^-n] F = sum_{c+d<=n} P_c(u) P_d(v) (p/2)^c (q/2)^d /(c! d!) * h_{n-c-d}(1,..,c+d)
        where h_k(1..s) is the complete homogeneous symmetric function,
        and h_{n-s}(1..s) = S2(n, s)  (verified separately).

  A_n = 2^n n! [Z^-n] F,   B_1 = A_1,  B_n = A_n - sum_{k=1}^{n-1} C(n-1,k-1) B_k A_{n-k}
        (cumulant recursion for log F; B_n = 2^n n! [Z^-n] log F).

  kappa_r = Im B_{2r-1} / (2^(4r-2) (2r-1)!).

Polynomials in (u,v) with Gaussian integer coefficients are dicts
{(a,b): (re, im)}.
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

def gi_conj(x):
    return (x[0], -x[1])

def vp(n):
    n = abs(n)
    return (n & -n).bit_length() - 1 if n else 10 ** 9

# ---------------------------------------------------------------- polynomials

PZERO = {(0, 0): (1, 0)}

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

def pscale_int(p, m):
    return {k: (z[0] * m, z[1] * m) for k, z in p.items()}

def p_im(p):
    """Imaginary part as integer-coefficient polynomial {(a,b): int}."""
    r = {}
    for k, z in p.items():
        if z[1]:
            r[k] = z[1]
    return r

def p_min_vp(p):
    return min((vp(z) for z in p.values()), default=10 ** 9)

def p_degree(p):
    return max((a + b for (a, b) in p), default=-1)

# ---------------------------------------------------------------- builders

def build_P(N):
    """P_l(u) for l=0..N as integer polys in u (v-exponent 0)."""
    P = [ {(0, 0): (1, 0)} ]
    for j in range(N):
        P.append(pmul(P[-1], {(1, 0): (1, 0), (0, 0): (-j * (j + 1), 0)}))
    return P

def build_Q(N):
    Q = [ {(0, 0): (1, 0)} ]
    for j in range(N):
        Q.append(pmul(Q[-1], {(0, 1): (1, 0), (0, 0): (-j * (j + 1), 0)}))
    return Q

def stirling2(N):
    S = [[0] * (N + 1) for _ in range(N + 1)]
    S[0][0] = 1
    for n in range(1, N + 1):
        for m in range(1, n + 1):
            S[n][m] = S[n - 1][m - 1] + m * S[n - 1][m]
    return S

def homog(N):
    """h_k(1..s) for 0<=k, 1<=s<=N, by direct DP (independent of S2 identity)."""
    # h_k(1..s) = h_k(1..s-1) + x_s * h_{k-1}(1..s)  generating in t:
    # prod_{j=1}^s 1/(1 - j t).  Compute coefficient lists.
    H = [[0] * (N + 1) for _ in range(N + 1)]  # H[s][k]
    H[0][0] = 1
    for s in range(1, N + 1):
        for k in range(N + 1):
            H[s][k] = H[s - 1][k]
            if k >= 1:
                H[s][k] += s * H[s][k - 1]
    return H

def Ctilde(N):
    """Ctilde_m = sum_l binom(m,l) P_l(u) P_{m-l}(v) p^l q^{m-l}, m=0..N."""
    P = build_P(N); Q = build_Q(N)
    # powers of p and q
    pp = [(1, 0)]; qq = [(1, 0)]
    for _ in range(N):
        pp.append(gi_mul(pp[-1], (1, 1)))
        qq.append(gi_mul(qq[-1], (1, -1)))
    C = []
    for m in range(N + 1):
        c = {}
        for l in range(m + 1):
            w = gi_mul(pp[l], qq[m - l])
            term = pmul(pmul(P[l], Q[m - l]), {(0, 0): w})
            c = padd(c, term, comb(m, l))
        C.append(c)
    return C

def compute_AB(N):
    """Return (A, B) lists of length N+1: A_n = 2^n n! [Z^-n] F (n=0..N),
    B_n the cumulants (B_0 unused = {})."""
    S = stirling2(N)
    H = homog(N)
    C = Ctilde(N)
    # cross-check h_{n-s}(1..s) = S2(n,s)
    for n in range(1, N + 1):
        for s in range(1, n + 1):
            assert H[s][n - s] == S[n][s], (n, s, H[s][n - s], S[n][s])
    A = [ {} ]
    for n in range(1, N + 1):
        p = {}
        for s in range(1, n + 1):
            # coefficient 2^n * n! * 2^{-s} * S2(n,s) * (Ctilde_s/s!)
            factor = 2 ** (n - s) * (factorial(n) // factorial(s)) * S[n][s]
            p = padd(p, C[s], factor)
        A.append(p)
    B = [ {} ]
    for n in range(1, N + 1):
        b = dict(A[n])
        for k in range(1, n):
            b = padd(b, pmul(B[k], A[n - k]), -comb(n - 1, k - 1))
        B.append(b)
    return A, B

def kappa_r_poly(B, r):
    """kappa_r * 2^(4r-2) (2r-1)! = Im B_{2r-1}; return Im B_{2r-1} and the
    rational polynomial kappa_r as dict {(a,b): Fraction}."""
    n = 2 * r - 1
    im = p_im(B[n])
    d = 2 ** (4 * r - 2) * factorial(2 * r - 1)
    kap = {k: Fraction(z, d) for k, z in im.items()}
    return im, kap

def I_r(r):
    """I_r = sum_{j=0}^{r-1} binom(r-1,j)/(2j+1)."""
    return sum(Fraction(comb(r - 1, j), 2 * j + 1) for j in range(r))

def main(N=24):
    A, B = compute_AB(N)
    out = []
    for r in range(1, (N + 1) // 2 + 1):
        im, kap = kappa_r_poly(B, r)
        m = r - 1
        row = {
            "r": r,
            "n": 2 * r - 1,
            "min_v2_ImB": p_min_vp(im),
            "proposed_3m": 3 * m,
            "delta_r_minus_proposed": -(p_min_vp(im) - 3 * m),  # 0 iff law holds
            "deg_ImB": p_degree(im),
            "nu2_pure_u^r": vp(im.get((r, 0), 0)),
            "proposed_pure": -(2 * r + vp(factorial(r - 1))) + (4 * r - 2 + vp(factorial(2 * r - 1))),
            "nu2_pure_minus_3m": vp(im.get((r, 0), 0)) - 3 * m,
        }
        # gamma_r estimate
        ir = I_r(r)
        pure = im.get((r, 0), 0)
        if pure:
            row["gamma_r"] = str(Fraction(pure, 2 ** (4 * r - 2) * factorial(2 * r - 1)) / ir)
        out.append(row)
        print(json.dumps(row), flush=True)
    return A, B, out

if __name__ == "__main__":
    import sys
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    main(N)
