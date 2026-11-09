# Exact second differences Delta_sym(1_B) = T(1_B)+T(-1_B)-2T(0), T(y)=E[Sh(X+y)], X_a=sum_{f(a)=1} e_f,
# for a profile m' ; printed in units h_o/(2t)  (t = n/7).  Also single-coordinate B={a}.
import sys; sys.path.insert(0, 'scripts')
from vk import np, fval
from math import comb
import itertools
ho = 0.00833056532535052
INC = [[fval(f, a) for f in range(1, 8)] for a in range(1, 8)]
def setup(m):
    vals = [np.arange(-k, k + 1, 2, dtype=np.int16) for k in m]
    wts = [np.array([comb(k, i) for i in range(k + 1)], dtype=np.float64) for k in m]
    shp = tuple(len(v) for v in vals)
    g = np.meshgrid(*vals, indexing='ij', sparse=True); wg = np.meshgrid(*wts, indexing='ij', sparse=True)
    W = wg[0]
    for x in wg[1:]: W = W * x
    W = np.broadcast_to(W, shp).reshape(-1) / 2.0 ** sum(m)
    X = np.stack([np.broadcast_to(sum(g[f] for f in range(7) if INC[a][f]), shp).reshape(-1) for a in range(7)])
    return X, W
def T(X, W, y):
    Z = X + np.array(y, dtype=np.int16)[:, None]
    ok = np.all(Z >= 0, axis=0); z = (Z == 0).sum(axis=0)
    return float((W * ok / (1 + z)).sum())
mp = tuple(int(x) for x in sys.argv[1:8]); t = sum(mp) / 7
X, W = setup(mp)
T0 = T(X, W, [0] * 7)
unit = ho / (2 * t)
def D(B):
    y = [1 if a in B else 0 for a in range(1, 8)]
    return (T(X, W, y) + T(X, W, [-q for q in y]) - 2 * T0) / unit
psi = 0
for f in range(1, 8):
    if mp[f - 1] % 2: psi ^= f
print("m'", mp, 't', round(t, 3), 'T0*8', T0 * 8, "psi'", psi)
for a in range(1, 8):
    print('  single a=%d parity %d: %.4f' % (a, fval(psi, a), D([a])))
for a, b in [(1, 2), (1, 3), (2, 3), (1, 6), (2, 4), (4, 5)]:
    print('  pair (%d,%d) parities (%d,%d): pair-part %.4f' % (a, b, fval(psi, a), fval(psi, b), D([a, b]) - D([a]) - D([b])))
g = 1
Bp = [a for a in range(1, 8) if fval(g, a) == 0]; B1 = [a for a in range(1, 8) if fval(g, a) == 1]
print('  Delta(v_perp) %.4f  Delta(v_1) %.4f  diff %.4f  (g=1)' % (D(Bp), D(B1), D(Bp) - D(B1)))
