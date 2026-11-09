# EXPLORATORY float64 profile (not a proof): a_{n+1}=expm1(t a_n), ordinary power series, k g_k = sum_j j f_j g_{k-j}.
import sys, json
import numpy as np
D = int(sys.argv[1]); N = int(sys.argv[2]); show = set(int(x) for x in sys.argv[3].split(','))
a = np.zeros(D + 1); f = 1.0
for k in range(1, D + 1):
    f *= -1.0 / k; a[k] = f  # e^{-t}-1
gmax = (0, 0, 0.0)
for n in range(1, N + 1):
    s = np.abs(a.copy()); s[:n + 1] = 0
    k = int(np.argmax(s))
    if s[k] > gmax[2]: gmax = (n, k, float(s[k]))
    if n in show:
        w = []
        for j in range(2, D // (n + 1) + 1):
            lo, hi = j * n, min((j + 1) * n, D + 1)
            kk = lo + int(np.argmax(np.abs(a[lo:hi]))); w.append(round(float(a[kk]) * j, 3))
        print(json.dumps({'n': n, 'j_times_window_max_j>=2': w})); sys.stdout.flush()
    fz = np.zeros(D + 1); fz[1:] = a[:-1]  # t*a_n
    jf = np.arange(D + 1) * fz
    g = np.zeros(D + 1); g[0] = 1.0
    for kk in range(1, D + 1):
        g[kk] = np.dot(jf[1:kk + 1], g[kk - 1::-1][:kk]) / kk
    a = g; a[0] = 0.0
print(json.dumps({'float_max_nonleading': gmax, 'D': D, 'N': N}))
