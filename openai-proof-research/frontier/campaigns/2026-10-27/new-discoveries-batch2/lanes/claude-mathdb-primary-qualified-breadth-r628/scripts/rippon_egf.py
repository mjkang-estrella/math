# Exact integer EGF computation: phi_t^n(-1) = sum_k b_{n,k} t^k / k!, b integers.
# a_1 = e^{-t}-1; a_{n+1} = exp(t a_n) - 1. Tests |b_{n,k}| > k! (coefficient modulus > 1).
import sys, json, math
D = int(sys.argv[1]); N = int(sys.argv[2])
C = [[1]]
for m in range(1, D + 1):
    r = C[-1]; C.append([1] + [r[j - 1] + r[j] for j in range(1, m)] + [1])
fact = [1]
for k in range(1, D + 1): fact.append(fact[-1] * k)
def exp_egf(f):  # f[0]==0; returns g=exp(f) EGF integer coefficients
    g = [0] * (D + 1); g[0] = 1
    for m in range(D):
        s = 0; Cm = C[m]
        for j in range(m + 1):
            if f[j + 1]: s += Cm[j] * f[j + 1] * g[m - j]
        g[m + 1] = s
    return g
a = [0] + [(-1) ** k for k in range(1, D + 1)]
rec = []
for n in range(1, N + 1):
    best = max(range(D + 1), key=lambda k: abs(a[k]) * 10**0 / fact[k] if a[k] else -1)
    ratio = [(k, abs(a[k]) / fact[k]) for k in range(D + 1) if a[k]]
    over = [(k, a[k]) for k in range(D + 1) if abs(a[k]) > fact[k]]
    top = sorted(ratio, key=lambda p: -p[1])[:3]
    tail = ratio[-1]
    r = {'n': n, 'top3': [(k, round(v, 6)) for k, v in top], 'deg_D_ratio': (tail[0], '%.4g' % tail[1]), 'count_gt1': len(over),
         'first_gt1': [(k, str(b), str(fact[k])) for k, b in over[:1]]}
    rec.append(r); print(json.dumps(r)); sys.stdout.flush()
    ta = [0] + [k * a[k - 1] for k in range(1, D + 1)]  # EGF of t*a_n
    a = exp_egf(ta); a[0] = 0
