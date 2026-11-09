import json, math
import numpy as np

out = {}
SQ2 = math.sqrt(2.0)

# --- quadrature: Z(s) = int_0^1 exp(-s/(x(1-x))) dx, via x=(1+tanh v)/2 ---
def _Z_simpson(s, n=1 << 16):
    V = math.acosh(math.sqrt(700.0/(4.0*s)))
    v = np.linspace(-V, V, n+1)
    ch = np.cosh(v); sech2 = 1.0/ch**2
    f = np.exp(-4.0*s*ch*ch)*0.5*sech2
    h = v[1]-v[0]
    return float(h*(f[0]+f[-1]+4*f[1:-1:2].sum()+2*f[2:-1:2].sum())/3.0)

def Z(s):
    a = _Z_simpson(s, 1 << 14); b = _Z_simpson(s, 1 << 16)
    return b, abs(b-a)

def cw(s):
    zs, e1 = Z(s)
    v, e2 = _Z_simpson(2*s, 1 << 16), 0.0
    return v/zs**2, max(e1, abs(v/_Z_simpson(2*s, 1 << 14) - 1))

# root c_w(s)=3
lo, hi = 2.0, 4.0
cw_lo, e1 = cw(lo); cw_hi, e2 = cw(hi)
assert cw_lo < 3 < cw_hi, (lo, cw_lo, hi, cw_hi)
for _ in range(60):
    mid = 0.5*(lo+hi)
    cwm, _ = cw(mid)
    if cwm < 3: lo = mid
    else: hi = mid
s_star = 0.5*(lo+hi)
cw_star, e_star = cw(s_star)
out['s_star'] = s_star; out['cw_at_s_star'] = cw_star
out['bracket'] = {'lo': lo, 'hi': hi, 'cw_lo': cw_lo, 'cw_hi': cw_hi}
out['cw_quad_err'] = e_star

lo2, hi2 = 0.2, 1.0
for _ in range(60):
    mid = 0.5*(lo2+hi2)
    cwm, _ = cw(mid)
    if cwm < 1.3: lo2 = mid
    else: hi2 = mid
s_wrong = 0.5*(lo2+hi2)
cw_wrong, _ = cw(s_wrong)
out['s_wrong'] = s_wrong; out['cw_wrong'] = cw_wrong

zs, ez = Z(s_star)
i52 = _Z_simpson(2.5*s_star, 1 << 16)
out['int_w_52_at_s_star'] = i52/zs**2.5
out['int_w_52_relcheck'] = abs(i52/_Z_simpson(2.5*s_star, 1 << 14) - 1)

xs = np.linspace(-8, 8, 200001)
phi = np.exp(-xs**2/2)/math.sqrt(2*math.pi)
M3 = float(np.max(np.abs((xs**3-3*xs)*phi)))
out['M3'] = M3; out['M3_x'] = float(xs[np.argmax(np.abs((xs**3-3*xs)*phi))])
out['M5'] = float(np.max(np.abs((xs**5-10*xs**3+15*xs)*phi)))
del xs, phi

def phi_f(x): return np.exp(-0.5*x*x)/math.sqrt(2*math.pi)
_erf = np.frompyfunc(math.erf, 1, 1)
def Phi_chunks(x):
    r = np.empty(len(x))
    for i0 in range(0, len(x), 1 << 19):
        blk = x[i0:i0+(1 << 19)]
        r[i0:i0+len(blk)] = np.asarray(_erf(blk/SQ2), dtype=np.float64)
    return 0.5*(1.0+r)

def G_of(x, N, k4):
    return Phi_chunks(x) - (k4/(8.0*N))*(x**3-3*x)*phi_f(x)

def weights(s, N):
    zs, _ = Z(s)
    wv = np.array([math.exp(-s/((n/N)*(1-n/N)))/zs if 0 < n/N < 1 else 0.0 for n in range(1, N)])
    A = float(wv.sum())  # A_N (w(0)=0)
    return np.sqrt(wv/A), A

def D_rademacher(s, N, k4=-2.0):
    b, A = weights(s, N)
    m = len(b)  # N-1 weights
    arr = np.empty(2**m)
    arr[0] = 0.0
    CH = 1 << 19
    for k in range(m):
        h = 2**k
        for i0 in range(0, h, CH):
            j1 = min(i0+CH, h)
            arr[h+i0:h+j1] = arr[i0:j1] - b[k]
        for i0 in range(0, h, CH):
            j1 = min(i0+CH, h)
            arr[i0:j1] += b[k]
    arr.sort()
    D = 0.0
    for i0 in range(0, len(arr), CH):
        x = arr[i0:i0+CH]
        j = np.arange(i0+1, i0+len(x)+1, dtype=np.float64)
        G = G_of(x, N, k4)
        D = max(D, float(np.max(np.abs(j/(2.0**m)-G))), float(np.max(np.abs((j-1)/(2.0**m)-G))))
    D = max(D, abs(float(G_of(np.array([float(arr[0])]), N, k4)[0])))  # F=0 below min atom
    D = max(D, abs(1.0 - float(G_of(np.array([float(arr[-1])]), N, k4)[0])))  # F=1 above max atom
    del arr
    return D

res = []
for N in [8, 12, 16, 20, 23]:
    D3 = D_rademacher(s_star, N)
    Dw = D_rademacher(s_wrong, N)
    res.append({'N': N, 'D_cw3': D3, 'D_cw3_x_N': D3*N, 'D_cw3_x_N1.5': D3*N**1.5,
                'D_wrong': Dw, 'D_wrong_x_N': Dw*N, 'D_wrong_x_N1.5': Dw*N**1.5})
out['rademacher'] = res
out['wrong_prediction_DxN'] = abs(cw_wrong-3.0)*2.0*M3/24.0

# Continuous witness X_eps: density phi(x)(1+H4(x)/24): k3=0, k4=+1 (int x^2 H4 phi = 0, int x^4 H4 phi = 24, analytic)
def D_Xeps(s, N, xs_eval):
    b, A = weights(s, N)
    T = 30.0*math.sqrt(N)
    nt = 1 << 18
    dt = T/nt
    acc_sin = np.zeros(len(xs_eval))
    erf_cache = {}
    for i0 in range(0, nt, 4096):
        t = (np.arange(i0, min(i0+4096, nt))+0.5)*dt + 1e-12
        lg = np.zeros(len(t))
        for n in range(len(b)):
            u = t*b[n]
            lg += -0.5*u*u + np.log1p(u**4/24.0)  # phi_X(t)=exp(-t^2/2)(1+t^4/24): int e^{itx} H4 phi = t^4 e^{-t^2/2}
        w = np.exp(lg)/t
        for xi, x in enumerate(xs_eval):
            acc_sin[xi] += np.sum(np.sin(t*x)*w)
    F = 0.5 + acc_sin*dt/math.pi
    G = G_of(np.asarray(xs_eval, dtype=np.float64), N, 1.0)
    return float(np.max(np.abs(F-G))), float(np.max(np.abs(F-Phi_chunks(np.asarray(xs_eval, dtype=np.float64)))))

xg = np.linspace(-6.0, 6.0, 481)
res2 = []
for N in [60, 120, 240]:
    D3, D0 = D_Xeps(s_star, N, xg)
    res2.append({'N': N, 'D_vs_G_cw3': D3, 'D_vs_G_cw3_x_N': D3*N, 'D_vs_G_cw3_x_N1.5': D3*N**1.5, 'D_vs_Phi': D0})
out['Xeps'] = res2

with open('decisive_results.json', 'w') as f:
    json.dump(out, f, indent=1)
print(json.dumps(out, indent=1))
