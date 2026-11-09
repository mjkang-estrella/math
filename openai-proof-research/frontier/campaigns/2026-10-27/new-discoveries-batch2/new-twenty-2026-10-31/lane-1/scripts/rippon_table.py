# Exact coefficients c_{n,k} of phi_t^n(-1), phi_t(z)=e^{tz}-1, via integer EGF recursion b_{n,k}=k! c_{n,k}.
import sys
from fractions import Fraction as F
D = int(sys.argv[1]); N = int(sys.argv[2])
C = [[1]]
for m in range(1, D + 1):
    r = C[-1]; C.append([1] + [r[j - 1] + r[j] for j in range(1, m)] + [1])
fact = [1]
for k in range(1, D + 1): fact.append(fact[-1] * k)
def exp_egf(f):
    g = [0] * (D + 1); g[0] = 1
    for m in range(D):
        s = 0; Cm = C[m]
        for j in range(m + 1):
            if f[j + 1]: s += Cm[j] * f[j + 1] * g[m - j]
        g[m + 1] = s
    return g
a = [0] + [(-1) ** k for k in range(1, D + 1)]
rows = []
for n in range(1, N + 1):
    rows.append([F(a[k], fact[k]) for k in range(D + 1)])
    ta = [0] + [k * a[k - 1] for k in range(1, D + 1)]
    a = exp_egf(ta); a[0] = 0
for n in range(1, N + 1):
    print(n, ' '.join('%.4f' % float(rows[n - 1][n + j]) for j in range(0, min(D - n + 1, 3 * n + 1))))
