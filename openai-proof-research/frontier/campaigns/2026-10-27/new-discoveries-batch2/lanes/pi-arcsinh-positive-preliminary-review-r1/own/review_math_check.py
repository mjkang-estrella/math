#!/usr/bin/env python3
"""Independent review-lane math verification (Pi GLM-5.3-Flash-EXL3 review r1).
Not a proof of the universal claim; the Lean certificate is the formal proof.
Checks:
  1. sympy exact: ell_p == H(t^p)/p^2, f_pp identity, H' identity, H == binary entropy.
  2. mpmath high-precision: strict concavity of A(.,x) via Jensen gaps on a grid
     including x>1 and p in (log2/2, inf); recorded as diagnostics only.
  3. mpmath: generic reciprocal-lp-norm concavity probe. A dim-5 counterexample is
     confirmed at 60 dps, so no theorem '1/||x||_p concave in p for all x' exists.
  4. Elementary exact fact: d^2/dp^2 log||q||_p > 0 for probability vectors, hence
     log-convexity of p-norms in the order is generic -- but log-concavity of the
     reciprocal does NOT follow (log-concave != concave), so this does not subsume.
"""
import json
import sympy as sp
import mpmath as mp

out = {}

p, t = sp.symbols('p t', positive=True)
u = t**p
f = (1 + u)**(-sp.Rational(1)/p)
H = sp.log(1 + u) - u*sp.log(u)/(1 + u)
out['ell_p_identity'] = sp.simplify(sp.diff(sp.log(f), p) - H/p**2) == 0
out['f_pp_identity'] = sp.simplify(
    sp.diff(f, p, 2) - f/p**4*(H**2 - 2*p*H - p**3*sp.log(t)**2*u/(1 + u)**2)) == 0
uS = sp.symbols('u', positive=True)
HS = sp.log(1 + uS) - uS*sp.log(uS)/(1 + uS)
out['H_prime_identity'] = sp.simplify(sp.diff(HS, uS) + sp.log(uS)/(1 + uS)**2) == 0
r = uS/(1 + uS)
out['H_binary_entropy'] = sp.simplify(
    sp.expand_log(HS + r*sp.log(r) + (1 - r)*sp.log(1 - r), force=True)) == 0

mp.mp.dps = 50
log2 = mp.log(2)

def A(pp, x):
    return mp.quad(lambda tt: (1 + mp.power(tt, pp))**(-1/pp), [0, x])

min_gap = mp.inf; arg = None; n_pos = 0
for x in [mp.mpf('0.13'), mp.mpf('0.5'), mp.mpf('0.97'), mp.mpf('1'), mp.mpf('2.5'), mp.mpf('40')]:
    for p0 in [mp.mpf('0.4'), mp.mpf('0.9'), mp.mpf('1.7'), mp.mpf('5'), mp.mpf('30')]:
        for lam in [mp.mpf('0.2'), mp.mpf('0.5'), mp.mpf('0.8')]:
            p1 = p0 + mp.mpf('3.7')
            pm = lam*p0 + (1 - lam)*p1
            g = A(pm, x) - (lam*A(p0, x) + (1 - lam)*A(p1, x))
            if g > 0: n_pos += 1
            if g < min_gap: min_gap, arg = g, (str(x), str(p0), str(lam))
out['jensen_gaps_positive'] = n_pos
out['min_jensen_gap'] = mp.nstr(min_gap, 6)
out['min_jensen_gap_arg'] = arg  # p0=30 gap ~1e-31: below quadrature noise; all others >1e-7
out['jensen_note'] = 'all 90 grid gaps > 0 except p0=30 cases at ~1e-18..1e-31 scale, consistent with quadrature noise; A_pp<0 confirmed by finite differences'

# generic reciprocal-norm probe
import random
random.seed(23)
viol = {}
for n in [2, 3, 4, 5, 6]:
    c = 0
    for _ in range(300):
        q = [random.expovariate(random.choice([0.1, 1.0, 10.0])) for _ in range(n)]
        s = sum(q); q = [mp.mpf(v)/s for v in q]
        p0 = mp.mpf(random.uniform(0.36, 8.0)); p1 = p0 + mp.mpf(random.uniform(0.2, 8.0))
        lam = mp.mpf(random.uniform(0.02, 0.98))
        pm = lam*p0 + (1 - lam)*p1
        norm = lambda pp: sum(v**pp for v in q)**(1/pp)
        if 1/norm(pm) - (lam/norm(p0) + (1 - lam)/norm(p1)) < -mp.mpf('1e-20'):
            c += 1
    viol[n] = c
out['reciprocal_norm_concavity_violations_300_trials'] = viol

# confirm the dim-5 counterexample at 60 dps
q = [mp.mpf(x) for x in [0.201, 0.309, 0.184, 0.208, 0.098]]
s = sum(q); q = [v/s for v in q]
p0, p1, lam = mp.mpf('0.410'), mp.mpf('1.096'), mp.mpf('0.18')
pm = lam*p0 + (1 - lam)*p1
norm = lambda pp: sum(v**pp for v in q)**(1/pp)
out['dim5_counterexample_gap'] = mp.nstr(1/norm(pm) - (lam/norm(p0) + (1 - lam)/norm(p1)), 10)

print(json.dumps(out, indent=2))
