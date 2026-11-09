"""Strict-majority (proper) variant of the GLT one-big-player family: T = N/2 + 1.
Same closed form as prior_check.closed (duplicated here to avoid an import)."""
from fractions import Fraction as Fr
from math import comb
def closed(a, m, T):
    big = sum(comb(m, s) for s in range(max(0, T - a), min(m, T - 1) + 1))
    unit = (comb(m - 1, T - a - 1) if 1 <= T - a <= m else 0) + (comb(m - 1, T - 1) if 1 <= T <= m else 0)
    return big, unit
for k in (16, 36, 64, 400):
    m = round(k ** 1.5); a = 2 * k; N = a + m; T = N // 2 + 1
    big, unit = closed(a, m, T)
    norm = Fr(big, big + m * unit); bound = Fr(2 * a, N)
    print(f"k={k} a={a} m={m} T={T} (2T>N:{2*T>N}) norm~{float(norm):.9f} 2w/N={bound} violates={norm > bound} abs-violates={Fr(big, 2**m) > bound}")
    assert 2 * T > N and norm > bound
