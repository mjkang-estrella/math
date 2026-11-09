# Profile of |coeff| of phi_t^n(-1) by degree (exact rationals, printed as floats); excludes nothing.
from fractions import Fraction as F
import sys, json, math
D = int(sys.argv[1]); N = int(sys.argv[2])
def mul(a, b):
    c = [F(0)] * (D + 1)
    for i, x in enumerate(a):
        if x:
            for j in range(D + 1 - i):
                if b[j]: c[i + j] += x * b[j]
    return c
def expm1(u):
    res = [F(0)] * (D + 1); p = [F(1)] + [F(0)] * D; k = 0; fact = 1
    while True:
        k += 1; p = mul(p, u); fact *= k
        if not any(p): break
        for i in range(D + 1): res[i] += p[i] / fact
    return res
t = [F(0), F(1)] + [F(0)] * (D - 1)
a = expm1([-x for x in t])
for n in range(1, N + 1):
    nz = [(i, a[i]) for i in range(D + 1) if a[i]]
    sub = [(i, x) for i, x in nz if i > n]
    m2 = max(sub, key=lambda p: abs(p[1])) if sub else None
    print(json.dumps({'n': n, 'lead': [nz[0][0], str(nz[0][1])], 'max_nonlead_deg': m2[0] if m2 else None, 'max_nonlead': float(m2[1]) if m2 else None,
                      'profile': ['%d:%.3g' % (i, float(x)) for i, x in nz[:12]], 'tail': ['%d:%.3g' % (i, float(x)) for i, x in nz[-3:]]}))
    a = expm1(mul(t, a))
