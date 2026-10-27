"""Exact series coefficients of G_{k,n}(q) = (q^{2k-1};q^2)_n / (q;q^2)_{n+1}."""
from fractions import Fraction

def mulby_linear(P, e, sign=-1):
    # P -> P * (1 - q^e)  if sign=-1 ; P*(1+q^e) if sign=+1
    L = len(P) + e
    res = [0]*L
    for i,v in enumerate(P):
        res[i] += v
        res[i+e] += sign*v
    return res

def G_num_den(k, n):
    """Return (N, D) integer lists: G = N/D as rational function."""
    N = [1]
    for i in range(n):
        N = mulby_linear(N, 2*k-1+2*i, -1)
    D = [1]
    for j in range(n+1):
        D = mulby_linear(D, 1+2*j, -1)
    return N, D

def series_coeffs(k, n, M):
    """coefficients c_0..c_M of the power series G_{k,n}."""
    N, D = G_num_den(k, n)
    c = [0]*(M+1)
    for m in range(M+1):
        s = N[m] if m < len(N) else 0
        for j in range(1, min(m, len(D)-1)+1):
            if D[j]:
                s -= D[j]*c[m-j]
        c[m] = s  # D[0] == 1
    return c

if __name__ == "__main__":
    # sanity: k=1 -> 1/(1-q^{2n+1}); k=2 -> 1/(1-q); k=3 -> (1-q^{2n+3})/((1-q)(1-q^3))
    for (k,n) in [(1,3),(2,3),(3,2),(3,5),(4,2)]:
        c = series_coeffs(k,n,40)
        print(k,n,"min coeff:", min(c), "first 20:", c[:20])
