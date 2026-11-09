# Monte Carlo (common random numbers) of the Gaussian-limit deviator score for uniform multiplicities:
#   Gamma(gamma) = P( sum_{f(a)=1} e_{f0} >= sum_{f(a)=0} e_{f1}  for all a != 0 ),
#   e_{f0} ~ N(0, 1-gamma_f), e_{f1} ~ N(0, gamma_f) independent, gamma in [0,1]^7 (gamma = c/t).
# NOT a proof: plausibility check of the macroscopic regime (Gamma < 1/8 away from gamma = 0).
import sys; sys.path.insert(0, 'scripts')
from vk import np, fval
import itertools
rng = np.random.default_rng(20261103)
N = 400000
Z0 = rng.standard_normal((N, 7)).astype(np.float32); Z1 = rng.standard_normal((N, 7)).astype(np.float32)
I1 = np.array([[fval(f, a) for f in range(1, 8)] for a in range(1, 8)], dtype=np.float32)  # a x f
I0 = 1 - I1
def Gam(g):
    g = np.asarray(g, dtype=np.float32)
    L = (Z0 * np.sqrt(1 - g)) @ I1.T; R = (Z1 * np.sqrt(g)) @ I0.T
    # identically-tied opponents (deviator co-located with player a): L_a == R_a == 0 for every voter
    tied = sum(1 for a in range(7) if all(g[f] == 1 for f in range(7) if I1[a, f]) and all(g[f] == 0 for f in range(7) if I0[a, f]))
    return float(np.mean(np.all(L >= R, axis=1))) / (1 + tied)
se = np.sqrt(0.125 * 0.875 / N)
print('MC std error ~ %.5f ; Gamma(0) = %.5f (exact 0.125)' % (se, Gam([0] * 7)))
for eps in [0.01, 0.02, 0.05]:
    g = [eps] + [0] * 6
    print('slope check gamma=(%.2f,0..): (8 Gamma - 1)/eps = %.4f  (predicted -6 h_o = -0.0500)' % (eps, (8 * Gam(g) - 1) / eps))
best = []
for g in itertools.product([0, 0.5, 1], repeat=7):
    if any(g): best.append((Gam(g), g))
for _ in range(1500):
    k = rng.integers(1, 8); g = np.zeros(7); idx = rng.choice(7, k, replace=False); g[idx] = rng.random(k)
    best.append((Gam(g), tuple(np.round(g, 3))))
for _ in range(300):
    g = rng.random(7) * rng.random() * 0.3
    best.append((Gam(g), tuple(np.round(g, 3))))
best.sort(reverse=True)
print('largest Gamma over %d gamma != 0 (x8):' % len(best))
for v, g in best[:10]:
    print('  %.5f' % (8 * v), g, ' |gamma|_1 = %.3f' % sum(g))
v_p = Gam([0, 0, 0, 0, 0, 0, 0])
print('corner gamma = 1_{f(a)=1} (deviator co-located with player a), 8*Gamma =', 8 * Gam([fval(f, 1) for f in range(1, 8)]))
for lo in [0.1, 0.25, 0.5, 1.0, 2.0]:
    sel = [(v, g) for v, g in best if sum(g) >= lo]
    v, g = max(sel)
    print('max 8*Gamma over |gamma|_1 >= %.2f : %.4f at %s (%d points)' % (lo, 8 * v, tuple(float(x) for x in g), len(sel)))
