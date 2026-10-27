"""Test whether the amplitude F(alpha,beta;Z) satisfies an off-diagonal
Z+4 difference equation with rational coefficient, i.e. whether

    G(v) := F(Z+4) Z(Z+2) / F(Z),   v = 1/Z,  1/(Z+4) = v/(1+4v),

has coefficients that look like a fixed rational function of (Z; A, B).
"""
import sys
from fractions import Fraction
from math import factorial, comb
sys.path.insert(0, 'scripts')
from jacobi_shifted_core import compute_AB

F0 = (Fraction(0), Fraction(0))
F1 = (Fraction(1), Fraction(0))

def fadd(p, q):
    r = dict(p)
    for k, z in q.items():
        a, b = r.get(k, F0)
        r[k] = (a + z[0], b + z[1])
    return {k: z for k, z in r.items() if z != F0}

def fscale(p, c):
    return {k: (z[0] * c, z[1] * c) for k, z in p.items()}

def fmul(p, q):
    r = {}
    for (a, b), x in p.items():
        for (c, d), y in q.items():
            k = (a + c, b + d)
            s, t = r.get(k, F0)
            r[k] = (s + x[0] * y[0] - x[1] * y[1], t + x[0] * y[1] + x[1] * y[0])
    return {k: z for k, z in r.items() if z != F0}

def series_mul(f, g, M):
    out = [{} for _ in range(M + 1)]
    for i, fi in enumerate(f):
        if not fi: continue
        for j, gj in enumerate(g):
            if i + j <= M and gj:
                out[i + j] = fadd(out[i + j], fmul(fi, gj))
    return out

def series_inv(f, M):
    g = [{} for _ in range(M + 1)]
    g[0] = f[0]
    for n in range(1, M + 1):
        s = {}
        for j in range(1, n + 1):
            if f[j]:
                s = fadd(s, fmul(f[j], g[n - j]))
        g[n] = fscale(s, Fraction(-1))
    return g

def main(N=9, M=6):
    A, B = compute_AB(N)
    Fv = [{(0, 0): F1}]
    for n in range(1, N + 1):
        c = Fraction(1, 2**n * factorial(n))
        Fv.append({k: (Fraction(z[0]) * c, Fraction(z[1]) * c) for k, z in A[n].items()})

    # F(Z+4): substitute v -> v/(1+4v)
    res = [{} for _ in range(M + 1)]
    for n in range(0, min(N, M) + 1):
        if not Fv[n]: continue
        for j in range(0, M - n + 1):
            c = Fraction(comb(n + j - 1, j)) * Fraction((-4) ** j, 1) if n >= 1 else (Fraction(1) if j == 0 else F0[0])
            if n == 0:
                c = Fraction(1) if j == 0 else Fraction(0)
            res[n + j] = fadd(res[n + j], fscale(Fv[n], c))
    FZ4 = res

    # (1 + 2v) as series
    one2v = [{(0, 0): F1}, {(0, 0): (Fraction(2), F0[1])}] + [{} for _ in range(M - 1)]
    num = series_mul(FZ4, one2v, M)          # F(Z+4) Z(Z+2) v^2
    Finv = series_inv(Fv, M)
    G = series_mul(num, Finv, M)             # = Z(Z+2) F(Z+4)/F(Z) * v^2
    for j in range(0, M + 1):
        print(f"v^{j}:", {k: (str(z[0]), str(z[1])) for k, z in sorted(G[j].items())})

if __name__ == "__main__":
    main()
