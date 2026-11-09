"""Exact checks for the infinitude proof of the 350973 counterexample frieze (quiddity
(1+r2, r2, 2r2, r2), r2 = sqrt2), in Z[sqrt2] as integer pairs (a, b) = a + b sqrt2.
(1) g(j) = f(j+8) - s f(j+4) + f(j) vanishes for j = 0, 1 (s = -2 + 2 sqrt2), where f(k) = m_{0,k};
    with 4-periodic coefficients this gives the progression identity for all j.
(2) Conjugate values y = a - b sqrt2 of f(r), f(r+4) (r = 0..3): y0*y1 <= 0 and |y1| > |y0|,
    decided exactly (no floats) via squares.
(3) The same 8-step identity for diagonals i = 1, 2, 3 (not needed, recorded)."""
import json
def mul(x, y): return (x[0]*y[0] + 2*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def sub(x, y): return (x[0]-y[0], x[1]-y[1])
def add(x, y): return (x[0]+y[0], x[1]+y[1])
q = [(1, 1), (0, 1), (0, 2), (0, 1)]
def diag(i, K):
    f = [(0, 0), (1, 0)]
    for k in range(K):
        j = i + k + 1
        f.append(sub(mul(q[j % 4], f[-1]), f[-2]))
    return f
s = (-2, 2)
out = {}
for i in range(4):
    f = diag(i, 40)
    out[f'diag{i}_g0_g1'] = [add(sub(f[j+8], mul(s, f[j+4])), f[j]) for j in (0, 1)]
    out[f'diag{i}_g_all_zero_upto30'] = all(add(sub(f[j+8], mul(s, f[j+4])), f[j]) == (0, 0) for j in range(30))
f = diag(0, 20)
def conj_sign(x):
    a, b = x[0], -x[1]   # a + b' sqrt2 with b' = -b
    if a >= 0 and b >= 0: return 0 if (a == 0 and b == 0) else 1
    if a <= 0 and b <= 0: return -1
    if a > 0: return 1 if a*a > 2*b*b else -1
    return 1 if 2*b*b > a*a else -1
def conj_abs_gt(x, y):
    # |conj x| > |conj y| exactly: compare (conj x)^2 - (conj y)^2 > 0 ; (a - b r2)^2 = a^2 + 2b^2 - 2ab r2
    ax, bx = x; ay, by = y
    A = (ax*ax + 2*bx*bx) - (ay*ay + 2*by*by); B = -2*ax*bx + 2*ay*by   # A + B r2 > 0 ?
    if A >= 0 and B >= 0: return A > 0 or B > 0
    if A <= 0 and B <= 0: return False
    if A > 0: return A*A > 2*B*B
    return 2*B*B > A*A
checks = []
for r in range(4):
    y0, y1 = f[r], f[r+4]
    checks.append(dict(r=r, f_r=y0, f_r4=y1, conj_sign_r=conj_sign(y0), conj_sign_r4=conj_sign(y1),
                       opposite_or_zero=conj_sign(y0)*conj_sign(y1) <= 0, abs_grows=conj_abs_gt(y1, y0)))
out['residue_checks_diag0'] = checks
out['f0_values_k0_to_12'] = f[:13]
out['conj_s'] = (-2, -2)
print(json.dumps(out))
