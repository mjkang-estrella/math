# Exact truncated power series in t for phi_t^n(-1), phi_t(z)=e^{tz}-1. Reports max |coeff| per n.
from fractions import Fraction as F
import sys, json
D = int(sys.argv[1]); N = int(sys.argv[2])
def mul(a, b):
    c = [F(0)] * (D + 1)
    for i, x in enumerate(a):
        if x:
            for j in range(D + 1 - i):
                if b[j]: c[i + j] += x * b[j]
    return c
def expm1(u):  # u has zero constant term
    res = [F(0)] * (D + 1); p = [F(1)] + [F(0)] * D; k = 0; fact = 1
    while True:
        k += 1; p = mul(p, u); fact *= k
        if not any(p): break
        for i in range(D + 1): res[i] += p[i] / fact
    return res
t = [F(0), F(1)] + [F(0)] * (D - 1)
a = expm1([-x for x in t])  # e^{-t}-1
out = []
for n in range(1, N + 1):
    m = max(range(D + 1), key=lambda i: abs(a[i]))
    big = [(i, str(a[i])) for i in range(D + 1) if abs(a[i]) > 1]
    out.append({'n': n, 'argmax_deg': m, 'max_abs': float(abs(a[m])), 'max_exact': str(a[m]), 'n_gt1': len(big), 'first_gt1': big[:3]})
    print(json.dumps(out[-1]))
    a = expm1(mul(t, a))
