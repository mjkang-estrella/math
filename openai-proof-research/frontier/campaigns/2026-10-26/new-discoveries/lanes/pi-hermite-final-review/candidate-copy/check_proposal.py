#!/usr/bin/env python3
"""Independent algebra/numerical checks, not a universal proof or Lean replay."""
from pathlib import Path
from fractions import Fraction as F
import json, math
import sympy as s
import mpmath as mp

mp.mp.dps = 65
m = s.symbols('m', integer=True, nonnegative=True)
v, k = s.symbols('v k', real=True)
E = 4*m+3
r = lambda z: 2*(4*z+3)**2/(2*(4*z+3)**2-1)
gamma_ratio = ((2*m+3)**2/(2*m+1)**2 * E/(E+4)
               * ((2*m+2)*(2*m+1)/(m+1)**2)**2 / 16)
assert s.factor(gamma_ratio-(1-1/(4*(m+1)**2*(4*m+7)))) == 0
delta_ratio_minus_one = s.factor(gamma_ratio*r(m)/r(m+1)-1)
expected = ((176*m*m+440*m+247)/
            (4*(m+1)**2*(4*m+7)**3*(32*m*m+48*m+17)))
assert s.factor(delta_ratio_minus_one-expected) == 0
q = 1-s.Rational(15,7)*v+s.Rational(65,42)*v*v
assert s.discriminant(q, v) < 0
tailpoly = s.Poly(2*(2*(4+k)+1)**2-s.Rational(22,7)**3*(5+k), k)
assert all(c > 0 for c in tailpoly.all_coeffs())
assert F(99,98)*F(49,50) == F(99,100)
assert F(3,94) < F(7,50)
assert F(25,72) > F(1,4)
assert sum(F(5,4)**i/math.factorial(i) for i in range(4)) > F(16,5)
assert sum(F(1)**i/math.factorial(i) for i in range(4)) > F(64,25)
assert F(196,121) > F(25,16)
assert 3 < mp.pi < F(22,7).numerator/F(22,7).denominator

def const(n):
    return mp.power(2,n)*mp.gamma(mp.mpf(n+1)/2)/mp.sqrt(mp.pi)

checks = []
for mi in range(501):
    ei = 4*mi+3
    gi = mp.pi*(2*mi+1)**2*mp.binomial(2*mi,mi)**2/(ei*mp.power(16,mi))
    ri = mp.mpf(2*ei*ei)/(2*ei*ei-1)
    assert gi < ri
    if mi >= 1:
        assert gi < mp.mpf(99)/98
checks.append('Wallis comparisons m=0..500 (evidence)')

# Literal polynomial recurrence, not a reimplementation of the energy argument.
def h(n, x):
    hm, hn = mp.mpf(1), 2*x
    if n == 0:
        return hm
    for j in range(1,n):
        hm, hn = hn, 2*x*hn-2*j*hm
    return hn

samples = 0
worst = mp.mpf(0)
for n in range(1,101):
    ei = 2*n+1
    ci = const(n)
    cutoff = mp.sqrt(ei)*(1-mp.pi/(2*ei))
    for j in range(201):
        x = mp.sqrt(ei)*j/100
        y = h(n,x)*mp.exp(-x*x/2)
        z = min(x,cutoff)
        ratio = abs(y)*mp.sqrt(1-z*z/ei)/ci
        worst = max(worst,ratio)
        assert ratio <= 1+mp.mpf('1e-58'), (n,str(x),str(ratio))
        samples += 1
checks.append(f'literal Hermite full clamped inequality {samples} samples (evidence)')

# Actual Foster--Krasikov Theorem 1 transcription for the prior-art comparison.
def foster_squared(n,x):
    Y = 2*n-x*x
    if n%2:
        K = (mp.sqrt(16*n*n-16*n+6)*mp.factorial(n)*mp.factorial(n-1)
             /(mp.sqrt(2*n-1)*mp.factorial((n-1)//2)**2))
    else:
        K = (2*n*mp.sqrt(4*n-2)*mp.factorial(n)**2
             /(mp.sqrt(8*n*n-8*n+3)*mp.factorial(n//2)**2))
    return (K*(2*Y*Y-4*Y+3)
            /mp.sqrt(Y*(4*Y**4-12*Y**3+9*Y*Y+10*n*Y-12*n))
            *mp.exp(15*x*x/(2*Y*(2*Y-3)**2)))
foster_ratios = {}
for n in [3,5,7,9,21,51,101]:
    ratio = foster_squared(n,mp.mpf(0))/const(n)**2
    assert ratio > 1
    foster_ratios[str(n)] = str(ratio)
checks.append('Foster upper bound exceeds target at zero for listed odd degrees')

result = {'status':'PASS: supporting algebra and finite evidence only',
          'symbolic_wall_is_ratio':str(s.factor(gamma_ratio)),
          'symbolic_delta_ratio_minus_one':str(delta_ratio_minus_one),
          'n1_quadratic_discriminant':str(s.discriminant(q,v)),
          'tail_polynomial_n_eq_4_plus_k':str(tailpoly.as_expr()),
          'literal_samples':samples, 'largest_sampled_ratio':str(worst),
          'foster_zero_squared_bound_to_target_ratios':foster_ratios,
          'checks':checks, 'formal_verified':False, 'discovery_credit':0}
out = Path(__file__).with_name('proposal-check.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
