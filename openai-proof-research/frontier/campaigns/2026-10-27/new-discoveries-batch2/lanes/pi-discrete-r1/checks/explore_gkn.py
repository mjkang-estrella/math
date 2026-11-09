"""Explore G_{k,n} = (q^{2k-1};q^2)_n/(q;q^2)_{n+1} coefficient structure.

Independent exact computations:
1. Full-coefficient positivity check via exact series division up to m0+period.
2. R_{k,n} = (q^{2k-1};q^2)_n/(q;q^2)_n coefficients r_i, and partial sums
   along residue classes mod (2n+1): G = R/(1-q^{2n+1}).
3. Where are the minima?
"""
from fractions import Fraction as F

def mulby(P, e, sign=-1):
    L = len(P)+e; res = [0]*L
    for i, v in enumerate(P):
        res[i] += v
        res[i+e] += sign*v
    return res

def ND(k, n):
    N = [1]
    for i in range(n): N = mulby(N, 2*k-1+2*i)
    D = [1]
    for j in range(n+1): D = mulby(D, 1+2*j)
    return N, D

def series(N, D, M):
    c = [F(0)]*(M+1)
    for m in range(M+1):
        s = F(N[m]) if m < len(N) else F(0)
        for j in range(1, min(m, len(D)-1)+1):
            if D[j]: s -= F(D[j])*c[m-j]
        c[m] = s
    return c

def lcm(a, b): return a*b//gcd(a, b)
from math import gcd

def check_full(k, n, maxM=None):
    """Exact check of all coefficients up to m0 + L where m0 = sum(A) bounds
    the numerator degree and L = lcm(1,3,...,2n+1)."""
    A = [2*k-1+2*i for i in range(n)]
    B = [1+2*j for j in range(n+1)]
    L = 1
    for b in B: L = lcm(L, b)
    m0 = sum(A) + L + 10   # beyond this the tail is exactly periodic
    M = m0
    if maxM: M = min(M, maxM)
    c = series(*ND(k, n), M)
    mn = min(c); am = c.index(mn)
    return mn, am, M, c

def R_coeffs(k, n, M):
    """R = (q^{2k-1};q^2)_n/(q;q^2)_n, coefficients 0..M."""
    N = [1]
    for i in range(n): N = mulby(N, 2*k-1+2*i)
    D = [1]
    for j in range(n): D = mulby(D, 1+2*j)
    return series(N, D, M)

def partial_sums_classes(k, n, M):
    """r_i for i in 0..M; partial sums along each class mod (2n+1)."""
    mod = 2*n+1
    r = R_coeffs(k, n, M)
    res = {}
    for c in range(mod):
        s = F(0); mn = None; where = None
        i = c
        while i <= M:
            s += r[i]
            if mn is None or s < mn: mn, where = s, i
            i += mod
        res[c] = (mn, where, s)
    return r, res

if __name__ == "__main__":
    import sys
    print("=== full positivity spot checks (exact) ===")
    for (k, n) in [(3,1),(3,2),(4,2),(5,3),(6,4),(4,5),(7,3),(5,8),(6,2),(4,3),(8,6),(10,3),(9,9)]:
        mn, am, M, c = check_full(k, n)
        print(f"(k,n)=({k},{n}): min coeff = {mn} at m={am} (checked to m={M})")
    print()
    print("=== R partial sums along classes mod 2n+1 ===")
    for (k, n) in [(5,3),(7,3),(10,5),(8,6),(6,2),(4,3)]:
        mod = 2*n+1
        M = 2000
        r, res = partial_sums_classes(k, n, M)
        mins = [(v[0], c, v[1]) for c, v in res.items()]
        mins.sort()
        print(f"(k,n)=({k},{n}) mod={mod}: worst classes {mins[:4]}")
        print(f"   r coeffs near min: ", [str(r[i]) for i in range(max(0,mins[0][2]-8), mins[0][2]+3)])
