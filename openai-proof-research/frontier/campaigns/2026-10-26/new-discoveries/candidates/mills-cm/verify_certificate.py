#!/usr/bin/env python3
"""Exact independent certificate checks; numerics are diagnostics, not the proof."""
from pathlib import Path
from math import comb, factorial
import json
import sympy as sp
import mpmath as mp

ROOT = Path(__file__).resolve().parent
c, t, u = sp.symbols('c t u')
r = [c, sp.Integer(-1)]
for n in range(40):
    r.append((n + 1) * r[n])
d = [c**2]
for n in range(40):
    value = sum(comb(n + 1, k) * r[k] * r[n + 1 - k] for k in range(n + 2))
    value += (n + 1) * sum(comb(n, k) * r[k] * d[n - k] for k in range(n + 1))
    d.append(sp.Poly(value, c).as_expr())
stored = json.loads((ROOT / 'derivative-table.json').read_text())
assert all(sp.Poly(d[n], c) == sp.Poly(sum(sp.Integer(a) * c**k
    for k, a in enumerate(stored[n])), c) for n in range(41))

coeffs = json.loads((ROOT / 'derivative40-polynomial.json').read_text())['coefficients_ascending']
p = sum(sp.Integer(a) * t**k for k, a in enumerate(coeffs))
assert sp.expand(p.subs(t, c**2) - d[40]) == 0
cert = json.loads((ROOT / 'bernstein-certificate.json').read_text())
a, b = sp.Rational(cert['a']), sp.Rational(cert['b'])
scaled = list(map(sp.Rational, cert['scaled_coefficients']))
assert len(scaled) == 22 and all(x < 0 for x in scaled)
bernstein = sum(scaled[k] * u**k * (1-u)**(21-k) for k in range(22))
assert sp.expand(p.subs(t, a + (b-a)*u) - bernstein) == 0
assert a == sp.Rational(3141592, 2000000) and b == sp.Rational(3141593, 2000000)

# A distinct diagnostic: Cauchy quadrature of the literal complex erfc formula.
# No derivative recurrence or series division is used in this computation.
mp.mp.dps = 120
def quotient(z):
    mills = mp.sqrt(mp.pi/2) * mp.exp(z*z/2) * mp.erfc(z/mp.sqrt(2))
    return mills*mills/(1-z*mills)
N, radius = 256, mp.mpf('0.5')
coefficient = sum(quotient(radius * mp.exp(2j*mp.pi*j/N)) *
    mp.exp(-2j*mp.pi*j*40/N) for j in range(N))/(N*radius**40)
derivative = coefficient * factorial(40)
exact_eval = mp.mpf(str(sp.N(p.subs(t, sp.pi/2), 110)))
relative_error = abs((derivative-exact_eval)/exact_eval)
assert relative_error < mp.mpf('1e-65')
result = {'exact_table_recurrence': True, 'exact_even_polynomial_identity': True,
    'exact_bernstein_identity': True, 'all_22_scaled_coefficients_negative': True,
    'derivative40_decimal': mp.nstr(exact_eval, 90),
    'independent_cauchy_relative_error': mp.nstr(relative_error, 20),
    'qualification': 'Exact algebra checks plus independent numerical diagnostic; full Lean endpoint pending.'}
(ROOT / 'certificate-check.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
