#!/usr/bin/env python3
"""Smoothed-endpoint re-tests for the near-singular cases: Durand q=-0.45,
bridge b=0.4/0.49, I_m(1) b=0.4.  mpmath only."""
import json
import mpmath as mp
from pathlib import Path

mp.mp.dps = 35
out = {}

def phi_int(func, alpha, cut=30.0):
    """int_0^cut func(phi) dphi where func ~ phi^{-alpha} at 0, alpha in (0,1)."""
    beta = 1 - alpha
    def smoothed(s):  # phi = s^{1/beta}, s in (0,1)
        phi = s ** (1 / beta)
        return func(phi) * (1 / beta) * s ** (1 / beta - 1)
    return mp.quad(smoothed, [0, 0.5, 1]) + mp.quad(func, [1, 2, 5, 10, 20, cut])

# ---------- Durand q = -0.45 ----------
def durand_lhs(q, x, y):
    return mp.besselk(q, x) * mp.besselk(q, y) / (x * y) ** q

def durand_rhs(q, x, y):
    coef = mp.power(2, q - 1) * mp.gamma(q) / mp.gamma(2 * q)
    def integrand(phi):
        w = mp.sqrt(x * x + y * y + 2 * x * y * mp.cosh(phi))
        return w ** (-q) * mp.besselk(q, w) * mp.sinh(phi) ** (2 * q)
    return coef * phi_int(integrand, -2 * q)

d45 = []
for q in ['-0.45', '-0.49', '-0.499']:
    for (x, y) in [('0.7', '2.3'), ('1.0', '1.0'), ('3.0', '5.0')]:
        qq, xx, yy = mp.mpf(q), mp.mpf(x), mp.mpf(y)
        lhs = durand_lhs(qq, xx, yy)
        rhs = durand_rhs(qq, xx, yy)
        d45.append({'q': q, 'x': x, 'y': y, 'lhs': mp.nstr(lhs, 15),
                    'rhs': mp.nstr(rhs, 15),
                    'rel_err': mp.nstr(abs(lhs - rhs) / abs(lhs), 6)})
out['durand_near_minus_half'] = d45

# ---------- Bridge b near 1/2 ----------
def f_b(s, b):
    return 2 * s ** (b / 2) * mp.besselk(b, 2 * mp.sqrt(s)) / mp.gamma(b)

def bridge_rhs(b, u, lam):
    c = 2 * mp.sqrt(u * (1 - u))
    def integrand(phi):
        return f_b(lam * (1 + c * mp.cosh(phi)), b) * mp.sinh(phi) ** (-2 * b)
    return 2 / mp.beta(b, mp.mpf('0.5') - b) * phi_int(integrand, 2 * b)

br = []
for bs in ['0.4', '0.45', '0.49', '0.499']:
    for us in ['0.05', '0.5']:
        for ls in ['0.3', '3.0']:
            b, u, lam = mp.mpf(bs), mp.mpf(us), mp.mpf(ls)
            lhs = f_b(lam * u, b) * f_b(lam * (1 - u), b)
            rhs = bridge_rhs(b, u, lam)
            br.append({'b': bs, 'u': us, 'lambda': ls,
                       'rel_err': mp.nstr(abs(lhs - rhs) / abs(lhs), 6)})
out['bridge_near_half'] = br

# ---------- I_m(1), b=0.4 (endpoint singularity (1-t^2)^{-0.9}) ----------
def I_m_smooth(b, m):
    alpha = b + mp.mpf('0.5')  # exponent of (1-t) near t=1
    beta = 1 - alpha
    def smoothed(s):  # 1 - t = s^{1/beta}, t = 1 - s^{1/beta}, s in (0,1)
        t = 1 - s ** (1 / beta)
        dt = -(1 / beta) * s ** (1 / beta - 1)
        return (t ** (2 * b + m - 1) * (1 - t * t) ** (-b - mp.mpf('.5'))
                * (t + 1) ** (-m)) * abs(dt)
    return mp.quad(smoothed, [0, 0.5, 1]) + mp.quad(
        lambda t: t ** (2 * b + m - 1) * (1 - t * t) ** (-b - mp.mpf('.5')) * (t + 1) ** (-m),
        [0, 0.5])

ib = []
for bs, ms in [('0.4', 1), ('0.49', 2), ('0.25', 1)]:
    b, m = mp.mpf(bs), ms
    val = I_m_smooth(b, m)
    closed = mp.power(2, -2 * b - m) * mp.beta(mp.mpf('.5') - b, 2 * b + m)
    ib.append({'b': bs, 'm': ms, 'numeric': mp.nstr(val, 18),
               'closed': mp.nstr(closed, 18),
               'rel_err': mp.nstr(abs(val - closed) / abs(val), 6)})
out['I_m_1_smoothed'] = ib

Path('_smooth_checks.json').write_text(json.dumps(out, indent=1))
print(json.dumps(out, indent=1))
