# Window maxima of |c_{n,k}| = |b_{n,k}|/k! over k in [j*n, (j+1)*n) for selected n (exact ints, float display).
import sys, json
from fractions import Fraction
D = int(sys.argv[1]); N = int(sys.argv[2]); show = set(int(x) for x in sys.argv[3].split(','))
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
gmax = (0, 0, 0.0)
for n in range(1, N + 1):
    for k in range(n + 1, D + 1):
        v = abs(Fraction(a[k], fact[k]))
        if v > gmax[2]: gmax = (n, k, float(v))
        if v > 1: print('EXCEED', n, k, a[k], fact[k]); sys.exit(3)
    if n in show:
        w = []
        for j in range(1, D // n + 1):
            ks = [k for k in range(j * n, min((j + 1) * n, D + 1))]
            if not ks: break
            kk = max(ks, key=lambda k: abs(Fraction(a[k], fact[k])))
            w.append('%d@%d:%.3g' % (j, kk, float(Fraction(a[kk], fact[kk]))))
        print(json.dumps({'n': n, 'windows': w})); sys.stdout.flush()
    ta = [0] + [k * a[k - 1] for k in range(1, D + 1)]
    a = exp_egf(ta); a[0] = 0
print(json.dumps({'max_nonleading_over_all_n_le_N_deg_le_D': gmax, 'D': D, 'N': N}))
