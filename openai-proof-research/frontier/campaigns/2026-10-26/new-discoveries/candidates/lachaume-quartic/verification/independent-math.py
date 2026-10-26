#!/usr/bin/env python3
"""Independent final-review rederivation. Distinct code path from both the
parent (pure fractions, ascending lists) and the preliminary review: use
numpy polynomial objects + Fraction exact arithmetic via sympy Poly, and
derive everything from the source statement directly."""
import json
from fractions import Fraction as F
from sympy import symbols, Poly, expand, sqrt, Rational, diff, S, simplify, powsimp
from sympy import resultant as sres

x = symbols('x')

# --- Source literal statement: n=p=4, a=(1,2,1,2,1), sigma_k in 4 variables.
a = [1, 2, 1, 2, 1]
sig = [S.One, None, None, None, None]

def elementary(v, k):
    # v: list of sympy expressions, n=4
    from itertools import combinations
    from math import prod
    return sum((prod(v[i] for i in c) for c in combinations(range(4), k)), S.Zero)

t = symbols('t')
diag = sum(a[k]*elementary([t]*4, k) for k in range(5))
assert expand(diag) == t**4 + 8*t**3 + 6*t**2 + 8*t + 1, diag
P = t**4 + 8*t**3 + 6*t**2 + 8*t + 1

# 1. Exact normalized Laguerre identity via polynomial arithmetic.
Pp = diff(P, t); Ppp = diff(P, t, 2)
expr = expand(4*P*Ppp - 3*Pp**2)
assert expr == expand(-144*(t**2 - 1)**2), expr
# Also check the literal source form: P*P'' + (1/n - 1) (P')^2 with n=4.
src_expr = expand(P*Ppp + Rational(1, 4)*Pp**2 - Pp**2)  # = P*P'' - 3/4 P'^2
assert expand(P*Ppp + (S(1)/4 - 1)*Pp**2) == expand(src_expr) == expand(-36*(t**2-1)**2)

# 2. h = P^{1/4} second derivative check: h'' = (4 P P'' - 3 P'^2)/(16 P^{7/4}).
h = P**(S(1)/4)
h2 = diff(h, t, 2)
# verify 16 P^{7/4} h'' = 4PP''-3P'^2 symbolically
check = (16 * P**(S(7)/4) * h2)
assert simplify(check - (4*P*Ppp - 3*Pp**2)) == 0, "h'' identity"

# 3. Nonreal root: factorization and exact root of first quadratic.
s = sqrt(3)
q1 = t**2 + (4 - 2*s)*t + 1
q2 = t**2 + (4 + 2*s)*t + 1
assert expand(q1*q2 - P) == 0
u = s - 2
v2 = 4*s - 6
assert v2 > 0  # since sqrt3 > 3/2
z = u  # real part; imaginary part = sqrt(v2)
# Check q1(z + i*sqrt(v2)) = 0 exactly: compute real/imag parts.
zr, zi = u, sqrt(v2)
w = zr + zi
# Real/imaginary parts by hand: w=u+i*sqrt(v2), u=s-2, v2=4s-6.
re_part = expand(u**2 - v2 + (4-2*s)*u + 1)
im_part = expand(2*u + (4-2*s))
assert simplify(re_part) == 0 and simplify(im_part) == 0, (re_part, im_part)

# resultant check: P has a nonreal root iff q1 (negative discriminant) divides it
assert sres(Poly(P, t), Poly(t**2 + (4-2*s)*t + 1, t, extension=s)) == 0
disc = expand((4-2*s)**2 - 4)
assert simplify(disc - (24 - 16*s)) == 0 and (24 - 16*s) < 0  # negative discriminant: 24-16√3 ≈ -3.7

# 4. Slice values with first coordinate 2.
g = sum(a[k]*elementary([S(2), t, t, t], k) for k in range(5))
assert expand(g - (5 + 12*t + 15*t**2 + 4*t**3)) == 0, g
for tv, val in [(Rational(1,20), Rational(2819,500)),
                (Rational(1,10), Rational(3177,500)),
                (Rational(3,20), Rational(7151,1000))]:
    assert g.subs(t, tv) == val, (tv, g.subs(tv))

# 5. Rational fourth-power witness bounds, exact.
L, U, R = Rational(15409,10000), Rational(15877,10000), Rational(16352,10000)
assert L**4 < Rational(2819,500)
assert Rational(3177,500) < U**4
assert R**4 < Rational(7151,1000)
assert U < (L + R)/2
gap = (L + R)/2 - U
assert gap == Rational(7, 20000)

# Independent sanity: the actual irrational midpoints violate concavity strictly.
import mpmath as mp
mp.mp.dps = 60
fa = mp.mpf(2819)/500; fc = mp.mpf(3177)/500; fb = mp.mpf(7151)/1000
lhs_ = mp.root(fc, 4); rhs_ = (mp.root(fa,4) + mp.root(fb,4))/2
assert lhs_ < rhs_, (lhs_, rhs_)
assert (rhs_ - lhs_) > 0

# 6. Diagonal concavity via exact h''<=0 on x>0: P>0 for x>0 and 4PP''-3P'^2 = -144(x^2-1)^2 <= 0.
Ppos = all(c > 0 for c in Poly(P, t).all_coeffs())
assert Ppos
# also g-slice curvature consistency (intuition only)
cg = expand(4*g*diff(g,t,2) - 3*diff(g,t)**2)
assert cg == 168 - 240*t - 612*t**2 - 240*t**3 - 48*t**4

# 7. Conjecture-3 translation invariance of Zaimi's example (verify the parent addendum's correction ourselves).
Rsh = expand((t+2)**4 - 1)
assert Rsh == t**4 + 8*t**3 + 24*t**2 + 32*t + 15
assert all(c > 0 for c in Poly(Rsh, t).all_coeffs())
assert expand(4*Rsh*diff(Rsh,t,2) - 3*diff(Rsh,t)**2) == expand(-48*(t+2)**2)
assert sres(Poly(Rsh, t), Poly(t**2 + 4*t + 5, t)) == 0  # roots -2±i nonreal

result = {
    "status": "PASS",
    "path": "sympy Poly/expand exact arithmetic (distinct from parent fractions-lists and preliminary sympy-scripts)",
    "diagonal": "f_(1,2,1,2,1)(t,t,t,t) == t^4+8t^3+6t^2+8t+1 exact",
    "laguerre": "4PP''-3(P')^2 == -144(t^2-1)^2 exact; source form P*P''+(1/4-1)(P')^2 == -36(t^2-1)^2 <= 0 on all R",
    "second_derivative_formula": "16*P^(7/4)*(P^(1/4))'' == 4PP''-3(P')^2 exact",
    "factorization_and_root": "P=(x^2+(4-2√3)x+1)(x^2+(4+2√3)x+1); z=√3-2+i√(4√3-6) exact root, imag>0; resultant with q1 = 0",
    "slice": "g(t)=5+12t+15t^2+4t^3; values 2819/500, 3177/500, 7151/1000 exact at t=1/20,1/10,3/20",
    "rational_witness": "L=15409/10000, U=15877/10000, R=16352/10000 exact; L^4<2819/500<...; gap 7/20000; 60-digit mp check f(C)^{1/4} < (f(A)^{1/4}+f(B)^{1/4})/2",
    "translation_invariance": "(x+2)^4-1 == x^4+8x^3+24x^2+32x+15, all coefficients >0, 4RR''-3(R')^2=-48(x+2)^2, nonreal roots -2±i: parent addendum correction INDEPENDENTLY CONFIRMED",
    "qualification": "Supporting exact computation for final review; credit 0."
}
# Parent portability adjustment: retain every mathematical assertion; print the result
# instead of writing into the original reviewer lane's relative commands directory.
print(json.dumps(result, indent=2))
