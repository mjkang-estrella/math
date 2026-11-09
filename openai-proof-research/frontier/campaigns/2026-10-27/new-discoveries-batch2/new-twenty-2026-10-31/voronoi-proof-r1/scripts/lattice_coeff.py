# O(1/t) coefficient of the one-coordinate move, via the step identity + local (Euler-Maclaurin)
# expansion.  Units u = h_o / sigma^2, sigma^2 = 2t, h_o = int phi^3 Phi^5.
# Per coordinate a in B (y = +-1_B):  continuum H_aa = -3u, lattice correction +3u (even) / -3u (odd).
# Per unordered pair {a,b} in B: P2(pi_a, pi_b) = 2-D lattice sum with unit density (computed here).
# Prediction:  t*(8 sigma(e_j) - 1) = 2 h_o * (Delta(v_perp) - Delta(v_1)).
from fractions import Fraction
import itertools, math
def h2(za, zb):
    if za < 0 or zb < 0: return Fraction(0)
    return Fraction(1, 1 + (za == 0) + (zb == 0))
def P2(pa, pb, R=40):
    s = Fraction(0)
    for i in range(-R, R + 1):
        for j in range(-R, R + 1):
            za, zb = pa + 2 * i, pb + 2 * j
            s += 4 * (h2(za + 1, zb + 1) + h2(za - 1, zb - 1) - 2 * h2(za, zb))
    return s
P = {(p, q): P2(p, q) for p in (0, 1) for q in (0, 1)}
print('pair coefficients P2 (continuum value 2):', {k: str(v) for k, v in P.items()})
def fval(f, a): return bin(f & a).count('1') & 1
def Delta(B, par):
    s = sum(0 if par[a] == 0 else -6 for a in B)
    s += sum(P[(par[a], par[b])] for a, b in itertools.combinations(B, 2))
    return s
ho = 0.00833056532535052
def predict(psi, g):
    par = {a: fval(psi, a) for a in range(1, 8)}
    Bp = [a for a in range(1, 8) if fval(g, a) == 0]
    B1 = [a for a in range(1, 8) if fval(g, a) == 1]
    d = Delta(Bp, par) - Delta(B1, par)
    return d, 2 * ho * float(d)
for name, psi, g in [('uniform t, any g (psi\'=g)', 1, 1), ('family g=f1 (psi\'=0)', 0, 1), ('family g!=f1 (psi\'=f1+g)', 3, 2),
                     ('continuum check: no lattice', None, 1)]:
    if psi is None:
        print(name, 'expected -6 h_o =', -6 * ho); continue
    d, val = predict(psi, g)
    print(name, ': Delta_perp - Delta_1 =', d, ' predicted lim t*(8 sigma - 1) =', round(val, 5))
# all reduced-parity functionals psi' relative to g
for psi in range(8):
    d, val = predict(psi, 1)
    print('  psi\'=%d g=1: coefficient %s -> %.5f %s' % (psi, d, val, 'PROFITABLE' if val > 0 else 'unprofitable'))
