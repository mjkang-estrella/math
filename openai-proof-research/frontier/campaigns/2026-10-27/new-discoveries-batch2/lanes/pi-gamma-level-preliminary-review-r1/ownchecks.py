#!/usr/bin/env python3
"""Independent reviewer checks (pi-gamma-level-preliminary-review-r1).

Deliberately DIFFERENT algorithm from root's check_candidate.py:
  - root: bisection on rho(s) solving F(x,s)=log c, concavity margins of rho.
  - here: (a) direct verification of the Euler-product bridge
               logGamma(s-x)+logGamma(s+x)-2logGamma(s) == sum_m -log(1-x^2/(s+m)^2),
            which the root asserted but only checked via a one-factor algebraic identity;
          (b) Newton solve in h of Gamma(h)Gamma(h+2x)/Gamma(h+x)^2 = c directly,
            then strict convexity of h_c tested by second central finite differences
            on a dense grid, INCLUDING x in (0,1);
          (c) independent symbolic re-derivation of g', g'';
          (d) anchor checks against source Lemma 15: h(1)=1, h'(1)=2 (c=2),
              and h(x) ~ x^2/log 2 growth.
Diagnostics only; not a proof certificate.
"""
import json
from pathlib import Path
import mpmath as mp
import sympy as sp

out = {}

# (c) independent symbolic derivation
u = sp.symbols('u', positive=True)
g = -sp.log(1 - u**-2)
gp = sp.simplify(sp.diff(g, u))
gpp = sp.simplify(sp.diff(g, u, 2))
assert sp.simplify(gp + 2/(u*(u**2-1))) == 0, gp
assert sp.simplify(gpp - 2*(3*u**2-1)/(u**2*(u**2-1)**2)) == 0, gpp
assert sp.simplify(gpp*(u**2*(u**2-1)**2)/2 - (3*u**2-1)) == 0
# positivity on u>1: numerator 3u^2-1>2>0
out['symbolic'] = {"g'": str(gp), "g''": str(gpp), "g''_positive_on_(1,inf)": True}

mp.mp.dps = 60

# (a) Euler product bridge, direct comparison (root did NOT check this numerically)
def F_loggamma(x, s):
    return mp.loggamma(s-x) + mp.loggamma(s+x) - 2*mp.loggamma(s)

def F_series(x, s, M=400000):
    # sum -log(1 - x^2/(s+m)^2) for m=0..M  (tail bounded by x^2 * sum_{m>M} 1/(s+m)^2)
    total = mp.mpf(0)
    x2 = mp.mpf(x)**2
    for m in range(M+1):
        d = (s+m)**2 - x2
        total -= mp.log(d/(s+m)**2)
    # rigorous tail: sum_{m>M} x^2/(s+m)^2 = x^2*psi_1(s+M+1); each -log(1-t) <= t/(1-t), t<=tmax
    tmax = x2/(s+M+1)**2
    tail = x2 * mp.polygamma(1, s+M+1) / (1 - tmax)
    return total, tail

bridge = []
for x, s in [('0.3','0.5'), ('1','2.5'), ('2','3'), ('0.05','7'), ('5','5.5'), ('1.5','30')]:
    a = F_loggamma(mp.mpf(x), mp.mpf(s))
    b, tail = F_series(mp.mpf(x), mp.mpf(s), M=200000)
    err = abs(a-b)
    ok = err < tail
    bridge.append({'x': x, 's': s, 'loggamma': mp.nstr(a, 30), 'series': mp.nstr(b, 30),
                   'abs_err': mp.nstr(err, 10), 'tail_bound': mp.nstr(tail, 10), 'within_bound': bool(ok)})
    assert ok, (x, s, err, tail)
out['euler_product_bridge'] = bridge

# (b) Newton solve in h directly: phi(h) = Gamma(h)Gamma(h+2x)/Gamma(h+x)^2 - c = 0
def phi(h, x, c):
    return mp.exp(mp.loggamma(h)+mp.loggamma(h+2*x)-2*mp.loggamma(h+x)) - c

def dphi(h, x):
    # d/dh log ratio = psi(h) + psi(h+2x) - 2psi(h+x)
    return mp.exp(mp.loggamma(h)+mp.loggamma(h+2*x)-2*mp.loggamma(h+x)) * \
           (mp.digamma(h)+mp.digamma(h+2*x)-2*mp.digamma(h+x))

def h_of_x(x, c):
    # R(h)=Gamma(h)Gamma(h+2x)/Gamma(h+x)^2 is STRICTLY DECREASING in h, from +inf (h->0+) to 1 (h->inf),
    # since log-derivative psi(h)+psi(h+2x)-2psi(h+x)<0 (trigamma strictly decreasing).
    x = mp.mpf(x); c = mp.mpf(c)
    lo = mp.mpf('1e-300'); hi = mp.mpf('1')
    while phi(hi, x, c) > 0:
        hi *= 2
        if hi > mp.mpf('1e200'): raise RuntimeError('no bracket')
    for _ in range(400):
        mid = (lo+hi)/2
        if phi(mid, x, c) > 0: lo = mid
        else: hi = mid
    h = (lo+hi)/2
    # Newton polish (R decreasing, derivative negative; Newton converges)
    for _ in range(6):
        h = h - phi(h, x, c)/dphi(h, x)
    return h

# anchor: source Lemma 15 values at c=2
h1 = h_of_x(1, 2)
out['anchor_h1'] = mp.nstr(h1, 40)          # expect 1
assert abs(h1-1) < mp.mpf('1e-40')

# h'(1) = 2 for c=2, via symmetric difference on h_of_x
eps = mp.mpf('1e-12')
hp1 = (h_of_x(1+eps, 2) - h_of_x(1-eps, 2)) / (2*eps)
out['anchor_hprime1'] = mp.nstr(hp1, 20)    # expect 2
assert abs(hp1-2) < mp.mpf('1e-6'), hp1

# large-x growth: h(x)/x^2 -> 1/log 2 (c=2)
xL = mp.mpf('3000')
hL = h_of_x(xL, 2)
ratio = hL/xL**2
out['anchor_asymptotic_h_over_x2'] = {'x': '3000', 'ratio': mp.nstr(ratio, 15),
                                      '1_over_log2': mp.nstr(1/mp.log(2), 15)}
assert abs(ratio - 1/mp.log(2)) < mp.mpf('0.01')

# strict convexity of h_c by second central differences on dense grids, incl. x<1
def second_diff(x, c, eps):
    return (h_of_x(x+eps, c) - 2*h_of_x(x, c) + h_of_x(x-eps, c)) / eps**2

conv = []
grids = {
    '2':  ['0.002','0.01','0.05','0.2','0.5','0.9','1','1.5','2','5','20','100'],
    '1.2':['0.002','0.05','0.5','2','20'],
    '1.01':['0.002','0.05','0.5','2','20'],
    '5':  ['0.002','0.05','0.5','2','20'],
    '100':['0.002','0.05','0.5','2','20'],
}
for cs, xs in grids.items():
    c = mp.mpf(cs)
    for xs_ in xs:
        x = mp.mpf(xs_)
        eps = x/mp.mpf(100) if x > mp.mpf('0.01') else mp.mpf('1e-7')
        sd = second_diff(x, c, eps)
        assert sd > 0, (cs, xs_, sd)
        conv.append({'c': cs, 'x': xs_, 'second_diff': mp.nstr(sd, 12), 'eps': mp.nstr(eps, 5)})
out['h_second_difference_positive'] = {'count': len(conv), 'all_positive': True, 'sample': conv[:14]}

# strictness sanity: compare against linear interpolation of h at two points (direct strict convexity)
strict = []
for cs in ['1.2','2','5','100']:
    c = mp.mpf(cs)
    for xa, xb in [('0.001','0.5'), ('0.5','3'), ('0.01','200')]:
        xa, xb = mp.mpf(xa), mp.mpf(xb)
        ha, hb = h_of_x(xa, c), h_of_x(xb, c)
        xm = (xa+xb)/2
        hm = h_of_x(xm, c)
        gap = (ha+hb)/2 - hm   # >0 iff strictly convex (midpoint)
        assert gap > 0, (cs, xa, xb, gap)
        strict.append({'c': cs, 'x0': mp.nstr(xa,8), 'x1': mp.nstr(xb,8), 'midpoint_gap': mp.nstr(gap, 30)})
out['h_midpoint_strict_convexity'] = strict

# cross-check against root's rho route at one point: F(rho(s),s)=log c consistency
def F(x, s): return mp.loggamma(s-x)+mp.loggamma(s+x)-2*mp.loggamma(s)
s = mp.mpf('2.5'); c = mp.mpf('2')
h = h_of_x(mp.mpf('2')-mp.mpf('0'), c)  # not used; instead check F(x, x+h) relation:
# for x=1.0, h=h_of_x(1,2): F(h, h+1) should equal log 2
hh = h_of_x(1, 2)
val = F(hh, hh+1)
out['cross_check_F_level'] = mp.nstr(val, 40)  # expect log 2
assert abs(val - mp.log(2)) < mp.mpf('1e-30')

result = {'status': 'PASS diagnostics (not a proof)', 'precision_dps': mp.mp.dps, 'data': out}
Path(__file__).with_name('ownchecks-result.json').write_text(json.dumps(result, indent=2, default=str)+'\n')
print('PASS: bridge verified within tail bound at 6 points; h(1)=1, h\'(1)=2, asymptotic ok;')
print(len(conv), 'positive second differences;', len(strict), 'positive midpoint gaps; cross-check log2 ok')
