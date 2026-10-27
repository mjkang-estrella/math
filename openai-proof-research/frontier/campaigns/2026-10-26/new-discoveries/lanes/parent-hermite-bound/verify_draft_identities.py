#!/usr/bin/env python3
"""Exact checks on the draft's displayed identities, not a full proof verifier."""
from pathlib import Path
import json
import sympy as s

ROOT = Path(__file__).resolve().parent
E, m, x, t = s.symbols("E m x t")
F = lambda q: q**3 - q**2 + 2*q + 1
b = s.Rational(22, 7)
R = b - b*b/(4*E)
P = (352947*(E-7)**4 + 6535179*(E-7)**3 + 40836159*(E-7)**2
     + 89231464*(E-7) + 19560668)
j1 = 2*x*t - (E-1) - t*t
D = lambda f: s.diff(f, x) + j1*s.diff(f, t)
j2, j3 = s.expand(D(j1)), s.expand(D(D(j1)))
q = E-x*x
Em = 4*m+3
ratio = (2*m+3)**2*Em/(4*(m+1)**2*(4*m+7))
checks = {
    "peak_certificate": s.factor((3*E-F(R))*117649*E**3-P) == 0,
    "Riccati_j1_at_stationary": s.expand(j1.subs(t,x)-(1-q)) == 0,
    "Riccati_j2_at_stationary": s.expand(j2.subs(t,x)-2*x) == 0,
    "Riccati_j3_at_stationary": s.expand(j3.subs(t,x)-(2-2*q*q)) == 0,
    "Wallis_delta_difference": s.factor(
        ratio*(1-1/(2*(Em+4)**2))-(1-1/(2*Em**2))
        -(176*m*m+440*m+247)/(8*(m+1)**2*Em**2*(Em+4)**3)) == 0,
    "exp_five_halves_partial4_exact": sum(
        s.Rational(5,2)**j/s.factorial(j) for j in range(5)) == s.Rational(4169,384),
    "exp_partial4_gt_required": bool(s.Rational(4169,384) > s.Rational(256,25)),
    "M_derivative_uniform_bracket_positive": bool(
        s.Rational(9,10)*s.Rational(47,49)*s.Rational(7,45)-s.Rational(3,98) > 0),
    "cos_sqrt2_Taylor_value": sum(
        (-1)**j*s.Rational(2)**j/s.factorial(2*j) for j in range(4)) == s.Rational(7,45),
    "sin_sqrt2_Taylor_factor": sum(
        (-1)**j*s.Rational(2)**j/s.factorial(2*j+1) for j in range(3)) == s.Rational(7,10),
}
assert all(checks.values()), checks
(ROOT / "paper-math-qa.json").write_text(json.dumps({
    "checks": checks,
    "qualification": "Exact symbolic identities/constants only; not a substitute for the complete mathematical proof, source review or full Lean endpoint."
}, indent=2) + "\n")

# An independent exact diagnostic for the preliminary review's reversed bound.
difference = (12*x-8*x**3)*s.exp(-x*x/2)-12/s.sqrt(7)*s.sin(s.sqrt(7)*x)
expansion = s.series(difference, x, 0, 9)
assert s.expand(expansion.removeO()).coeff(x, 5) == s.Rational(3, 5)
assert s.expand(expansion.removeO()).coeff(x, 7) == -s.Rational(13, 30)
(ROOT / "review-bound-direction-check.json").write_text(json.dumps({
    "actual_signed_n3": "(12*x-8*x^3)*exp(-x^2/2)",
    "claimed_upper": "12/sqrt(7)*sin(sqrt(7)*x)",
    "actual_minus_claimed_Taylor": str(expansion),
    "value_at_one_quarter_sanity_only": str(s.N(difference.subs(x, s.Rational(1,4)), 40)),
    "conclusion": "The positive leading x^5 coefficient makes the claimed upper comparison false near zero. The parent proof uses the correct lower direction."
}, indent=2) + "\n")
print(f"PASS: {len(checks)} exact draft identities/constants; reversed-review-bound diagnostic")
