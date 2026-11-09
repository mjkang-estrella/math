# Exact check of (L1) closed Stirling formula vs EGF recursion and (L2) stabilization, for n<=7, k<=22.
from fractions import Fraction as F
from functools import lru_cache
from math import factorial
D = 22; N = 7
@lru_cache(None)
def S2(n, k):
    if n == k: return 1
    if k == 0 or k > n: return 0
    return k * S2(n - 1, k) + S2(n - 1, k - 1)
def series_rec():
    a = [F(0)] + [F((-1) ** k, factorial(k)) for k in range(1, D + 1)]; rows = [a]
    for n in range(2, N + 1):
        b = [F(0)] + a[:-1]  # t*a
        # exp(b)-1 via g' = b' g
        g = [F(0)] * (D + 1); g[0] = F(1)
        for m in range(1, D + 1): g[m] = sum(j * b[j] * g[m - j] for j in range(1, m + 1)) / m
        g[0] = F(0); a = g; rows.append(a)
    return rows
def closed(n, k):
    tot = F(0)
    def rec(ms, left):
        nonlocal tot
        if len(ms) == n:
            if left == 0:
                v = F((-1) ** ms[-1], factorial(ms[-1]))
                for i in range(n - 1): v *= S2(ms[i + 1], ms[i])
                tot += v
            return
        lo = ms[-1] if ms else 1
        for m in range(lo, left + 1): rec(ms + [m], left - m)
    rec([], k); return tot
R = series_rec()
assert all(R[n - 1][k] == closed(n, k) for n in range(1, N + 1) for k in range(1, D + 1)), 'L1 mismatch'
assert all(R[n][n + 1 + j] == R[n - 1][n + j] for n in range(1, N) for j in range(0, n + 1) if n + 1 + j <= D), 'L2 mismatch'
assert all(k == 0 or (R[n - 1][k] * factorial(k)).denominator == 1 for n in range(1, N + 1) for k in range(D + 1))
print('L1, L2, integrality OK for n<=%d, k<=%d; s_0..s_5 =' % (N, D), [str(R[6][7 + j]) for j in range(6)])
