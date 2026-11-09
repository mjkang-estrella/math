# MIT License. Author: Myeongjin Kang. Exact polynomial certificates for (S)_n by sign pattern (exploration).
# Pattern (k,l,z): k positive coefficients u_1>=...>=u_k>0, l negative -v_1<=...<=-v_l<0, z zeros.
# Ordered variables: x_1..x_k >= 0 (x_k>0), y_1..y_l >= 0 (y_l>0) with u_i = x_i+...+x_k, v_j = y_j+...+y_l.
# Target polynomial T = C * NP * Den - D * Np^2 where p = Np/Den, E W^+ = NP/Den, Den = prod_{i,j}(u_i+v_j).
import sys
from fractions import Fraction as Fr
from poly import P

def build(k, l, z, n=None):
    if n is None: n = k + l + z
    nv = k + l
    X = [P.var(i, nv) for i in range(k)]
    Y = [P.var(k + j, nv) for j in range(l)]
    u = [sum(X[i:], P.const(0, nv)) for i in range(k)]
    v = [sum(Y[j:], P.const(0, nv)) for j in range(l)]
    def vand(lst):
        r = P.const(1, nv)
        for a in range(len(lst)):
            for b in range(a + 1, len(lst)):
                r = r * (lst[a] - lst[b])
        return r
    def num(extra):
        tot = P.const(0, nv)
        for i in range(k):
            others = [u[a] for a in range(k) if a != i]
            term = (u[i] ** (k - 1 + l + extra)) * vand(others)
            for a in range(k):
                if a != i:
                    for j in range(l): term = term * (u[a] + v[j])
            tot = tot + (term if i % 2 == 0 else -term)
        # divide by Vandermonde of u, factor by factor (u_a-u_b = x_a+...+x_{b-1})
        for a in range(k):
            for b in range(a + 1, k):
                tot = tot.divexact(u[a] - u[b])
        return tot
    Np = num(0); NP = num(1)
    Den = P.const(1, nv)
    for i in range(k):
        for j in range(l): Den = Den * (u[i] + v[j])
    # D(b) for sorted list: -v_1..-v_l, 0*z, u_k..u_1
    srt = [-v[j] for j in range(l)] + [P.const(0, nv)] * z + [u[i] for i in reversed(range(k))]
    m = len(srt)
    D = P.const(0, nv)
    for i, s in enumerate(srt): D = D + (2 * i - m + 1) * s
    return Np, NP, Den, D, nv

def check(k, l, z, C, n=None):
    Np, NP, Den, D, nv = build(k, l, z, n)
    T = C * NP * Den - D * Np * Np
    neg = T.neg_terms()
    return T, neg

if __name__ == "__main__":
    import random
    from s4 import pP, D as Db
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    for k in range(1, n + 1):
        for l in range(0, n - k + 1):
            z = n - k - l
            Np, NP, Den, D, nv = build(k, l, z)
            # numeric sanity check of p, P, D against independent formulas
            xs = [random.uniform(0.1, 1) for _ in range(nv)]
            u = [sum(xs[i:k]) for i in range(k)]; v = [sum(xs[k + j:]) for j in range(l)]
            b = u + [-t for t in v] + [0.0] * z
            p, PP = pP(b)
            ok = abs(Np(*xs) / Den(*xs) - p) < 1e-9 and abs(NP(*xs) / Den(*xs) - PP) < 1e-9 and abs(D(*xs) - Db(b)) < 1e-9
            T, neg = check(k, l, z, n + 1)
            print((k, l, z), "formula-ok", ok, "terms", len(T.t), "neg", len(neg), "min", T.mincoef(), flush=True)
