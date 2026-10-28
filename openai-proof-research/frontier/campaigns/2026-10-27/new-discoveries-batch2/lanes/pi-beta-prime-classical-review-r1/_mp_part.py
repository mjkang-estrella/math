#!/usr/bin/env python3
"""Independent adversarial review checks for root-beta-prime-addition-r19 (pi review lane).
Single process; mpmath for high precision, scipy only for the nested end-to-end LT check.
Numerics are diagnostics, not proof. Writes review_checks_raw.json in this lane."""
import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 40
out = {}

# ---------- 1. Durand display (D) as transcribed, direct high-precision test ----------
# K_q(x)K_q(y)/(xy)^q = 2^{q-1} Gamma(q)/Gamma(2q) *
#   int_0^inf w^{-q} K_q(w) sinh(phi)^{2q} dphi,  w = sqrt(x^2+y^2+2xy cosh phi)
def durand_lhs(q, x, y):
    return mp.besselk(q, x) * mp.besselk(q, y) / (x * y) ** q

def durand_rhs(q, x, y):
    coef = mp.power(2, q - 1) * mp.gamma(q) / mp.gamma(2 * q)
    def integrand(phi):
        w = mp.sqrt(x * x + y * y + 2 * x * y * mp.cosh(phi))
        return w ** (-q) * mp.besselk(q, w) * mp.sinh(phi) ** (2 * q)
    return coef * mp.quad(integrand, [0, 0.5, 1, 2, 5, 10, 20, 30])

durand = []
for q in ['-0.45', '-0.25', '-0.1', '0.3', '1.7']:
    for (x, y) in [('0.7', '2.3'), ('1.0', '1.0'), ('3.0', '5.0')]:
        qq, xx, yy = mp.mpf(q), mp.mpf(x), mp.mpf(y)
        lhs = durand_lhs(qq, xx, yy)
        rhs = durand_rhs(qq, xx, yy)
        rel = abs(lhs - rhs) / abs(lhs)
        durand.append({'q': q, 'x': x, 'y': y,
                       'lhs': mp.nstr(lhs, 12), 'rhs': mp.nstr(rhs, 12),
                       'rel_err': mp.nstr(rel, 6)})
out['durand_direct'] = durand

# ---------- 2. Bridge (E): f_b(lu) f_b(l(1-u)) = [2/B(b,1/2-b)] int f_b(l(1+c cosh)) sinh^{-2b} ----------
def f_b(s, b):
    return 2 * s ** (b / 2) * mp.besselk(b, 2 * mp.sqrt(s)) / mp.gamma(b)

def bridge_rhs(b, u, lam):
    c = 2 * mp.sqrt(u * (1 - u))
    def integrand(phi):
        return f_b(lam * (1 + c * mp.cosh(phi)), b) * mp.sinh(phi) ** (-2 * b)
    return 2 / mp.beta(b, mp.mpf('0.5') - b) * mp.quad(integrand, [0, 0.5, 1, 2, 5, 10, 20, 30])

bridge = []
for bs in ['0.1', '0.25', '0.4', '0.49']:
    for us in ['0.05', '0.5']:
        for ls in ['0.3', '3.0']:
            b, u, lam = mp.mpf(bs), mp.mpf(us), mp.mpf(ls)
            lhs = f_b(lam * u, b) * f_b(lam * (1 - u), b)
            rhs = bridge_rhs(b, u, lam)
            rel = abs(lhs - rhs) / abs(lhs)
            bridge.append({'b': bs, 'u': us, 'lambda': ls, 'rel_err': mp.nstr(rel, 6)})
out['bridge_E'] = bridge

# ---------- 3. Reciprocal moment identity on a fresh, harder grid ----------
def beta_expect_mp(f, a, q):
    half = mp.mpf('.5')
    lo = half ** a / a * mp.quad(
        lambda r: f(half * r ** (1 / a)) * (1 - half * r ** (1 / a)) ** (q - 1), [0, 1])
    hi = half ** q / q * mp.quad(
        lambda r: f(1 - half * r ** (1 / q)) * (1 - half * r ** (1 / q)) ** (a - 1), [0, 1])
    return (lo + hi) / mp.beta(a, q)

moms = []
worst = mp.mpf(0)
for bs in ['0.02', '0.49', '0.3']:
    for us in ['0.01', '0.5']:
        for mm in [1, 5, 30]:
            b, u = mp.mpf(bs), mp.mpf(us)
            c = 2 * mp.sqrt(u * (1 - u))
            lhs = mp.rf(2 * b, mm) * beta_expect_mp(
                lambda v: (v * (1 - v) / (u + (1 - 2 * u) * v)) ** mm, b, b)
            rhs = mp.rf(b, mm) * beta_expect_mp(
                lambda w: (mp.sqrt(w) / (mp.sqrt(w) + c)) ** mm, b, mp.mpf('.5') - b)
            ser = (mp.rf(2 * b, mm) * mp.rf(b, mm) /
                   (2 ** mm * mp.rf(b + mp.mpf('.5'), mm)) *
                   mp.hyp2f1(mp.mpf(mm) / 2, mp.mpf(mm + 1) / 2,
                             b + mm + mp.mpf('.5'), 1 - c * c))
            rel = max(abs(lhs - rhs), abs(lhs - ser)) / abs(lhs)
            worst = max(worst, rel)
            moms.append({'b': bs, 'u': us, 'm': mm, 'rel_err': mp.nstr(rel, 6)})
out['reciprocal_moments_fresh_grid'] = moms
out['reciprocal_moments_worst'] = mp.nstr(worst, 6)

# ---------- 4. Boundary value I_m(1) = 2^{-2b-m} B(1/2-b, 2b+m) ----------
def I_m(c, b, m):
    return mp.quad(lambda t: t ** (2 * b + m - 1) * (1 - t * t) ** (-b - mp.mpf('.5'))
                   * (t + c) ** (-m), [0, 1])

ib = []
for bs, ms in [('0.25', 1), ('0.25', 4), ('0.4', 1), ('0.1', 3)]:
    b, m = mp.mpf(bs), ms
    val = I_m(1, b, m)
    closed = mp.power(2, -2 * b - m) * mp.beta(mp.mpf('.5') - b, 2 * b + m)
    rel = abs(val - closed) / abs(val)
    ib.append({'b': bs, 'm': ms, 'numeric': mp.nstr(val, 15),
               'closed': mp.nstr(closed, 15), 'rel_err': mp.nstr(rel, 6)})
out['I_m_1_boundary'] = ib

# ---------- 6. 4U(1-U) ~ Beta(a, 1/2) ----------
def four_check(a):
    a = mp.mpf(a)
    def density(y):
        s = mp.sqrt(1 - y)
        jac = 1 / (4 * s)
        def bpdf(u):
            return u ** (a - 1) * (1 - u) ** (a - 1) / mp.beta(a, a)
        return (bpdf((1 + s) / 2) + bpdf((1 - s) / 2)) * jac
    def bpdf(y):
        return y ** (a - 1) * (1 - y) ** (mp.mpf('-0.5')) / mp.beta(a, mp.mpf('.5'))
    errs = []
    for ys in ['0.1', '0.5', '0.9']:
        y = mp.mpf(ys)
        errs.append(mp.nstr(abs(density(y) - bpdf(y)) / bpdf(y), 6))
    return errs
out['four_u_check_a1.3'] = four_check('1.3')
out['four_u_check_a0.4'] = four_check('0.4')

Path('_mp_checks.json').write_text(json.dumps(out, indent=1))
print(json.dumps(out, indent=1))
