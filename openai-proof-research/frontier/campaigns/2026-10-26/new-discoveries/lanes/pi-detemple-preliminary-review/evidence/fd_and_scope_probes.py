#!/usr/bin/env python3
"""Independent probes of the qualitative routes and scope limits.

1. FD identity D_{a0}(x)/x^2 -> +inf (PROOF.md route 2) - verified numerically.
2. G''_{a0}(x) -> +inf as x->0+ (PROOF.md route 1) - verified numerically.
3. SCOPE TEST: is the FD failure stronger than at a0 alone? For general a,
   D_a(x) -> 24*c*log(4/3) with c=7a/40-31/336 (analytic prediction), which is
   NEGATIVE for a<a0. Numerics below confirm: for a<a0 the second differences of
   G_a tend to a negative constant, so the FD refutation does NOT extend below a0
   by this route; the parent's scoping (exact a0 + continuity) is the correct one.
   An earlier reviewer hypothesis of failure for all a<a0 was refuted twice.
4. 7*(155/294)/40 == 31/336 exactly (c vanishes at a0).
"""
import mpmath as mp
mp.mp.dps = 50

def G(a, t):
    return 24*(t**4 + a*t**2 + mp.mpf(7)*a/40 - mp.mpf(31)/336)*(mp.digamma(t+mp.mpf('0.5')) - mp.log(t)) - t**2 + mp.mpf(7)/40 - a

a0 = mp.mpf(155)/294
print("FD route at a0: D(x)/x^2 (should -> +inf)")
for t in ['0.1','0.01','0.001']:
    t = mp.mpf(t)
    print("  x=%s: %s" % (t, mp.nstr((G(a0,3*t)-2*G(a0,2*t)+G(a0,t))/t**2, 20)))

print("G''_{a0}(x) (should -> +inf):")
for t in ['0.1','0.01','0.001','0.0001']:
    t = mp.mpf(t)
    print("  x=%s: %s" % (t, mp.nstr(mp.diff(lambda s: G(a0,s), t, 2), 15)))

print("Scope test: D_a(x) vs predicted limit 24*c*log(4/3):")
for a in ['0.5','0.1','0.527']:
    a = mp.mpf(a)
    c = mp.mpf(7)*a/40 - mp.mpf(31)/336
    pred = 24*c*mp.log(mp.mpf(4)/3)
    print(f"  a={a}: c={mp.nstr(c,8)}, predicted D limit = {mp.nstr(pred,12)}")
    for t in ['0.01','0.001','0.0001']:
        t = mp.mpf(t)
        print("     D_a(%s) = %s" % (t, mp.nstr(G(a,3*t)-2*G(a,2*t)+G(a,t), 12)))

from fractions import Fraction as F
print("7*(155/294)/40 == 31/336:", F(7,40)*F(155,294) == F(31,336))
