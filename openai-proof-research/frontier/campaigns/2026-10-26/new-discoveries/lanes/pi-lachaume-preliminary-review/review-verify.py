#!/usr/bin/env python3
"""Independent review rederivation (sympy path, distinct from parent's Fraction script).
Restored copy; canonical run output in commands/review-verify-output.txt."""
import sympy as sp
from sympy import Rational as R
import json, itertools

x = sp.Symbol('x')
t = sp.Symbol('t', real=True)
out = {}

P = x**4 + 8*x**3 + 6*x**2 + 8*x + 1
lhs = sp.expand(4*P*sp.diff(P, x, 2) - 3*sp.diff(P, x)**2)
out['identity_lhs'] = sp.sstr(lhs)
out['identity_check'] = sp.sstr(sp.expand(lhs + 144*(x**2 - 1)**2)) == '0'

q1 = x**2 + (4 - 2*sp.sqrt(3))*x + 1
q2 = x**2 + (4 + 2*sp.sqrt(3))*x + 1
out['factorization'] = sp.sstr(sp.expand(q1*q2)) == sp.sstr(P)
d1 = sp.discriminant(q1, x); d2 = sp.discriminant(q2, x)
out['discs'] = [sp.sstr(sp.simplify(d1)), sp.sstr(sp.simplify(d2))]
out['P_positive_all_R'] = bool((sp.simplify(d1) < 0) and (sp.simplify(d2) < 0))  # False: real roots negative; P>0 on x>0 only

s = sp.sqrt(3)
z = (s - 2) + sp.I*sp.sqrt(4*s - 6)
out['z_is_root'] = sp.sstr(sp.simplify(P.subs(x, z))) == '0'
out['z_imag_positive'] = bool(sp.sqrt(4*s - 6) > 0)
out['P_leading_pos'] = True
out['all_roots'] = [sp.sstr(sp.nsimplify(r)) for r in sp.solve(P, x)]

xs = sp.symbols('x1:5')
sig = [sp.Integer(1)]
for k in range(1, 5):
    sig.append(sp.expand(sum(sp.prod(c) for c in itertools.combinations(xs, k))))
a = [1, 2, 1, 2, 1]
f = sum(a[k]*sig[k] for k in range(5))
diag = sp.expand(f.subs({v: x for v in xs}))
out['diagonal_is_P'] = sp.sstr(diag) == sp.sstr(P)
g = sp.expand(f.subs({xs[0]: 2, xs[1]: t, xs[2]: t, xs[3]: t}))
out['g'] = sp.sstr(g)
out['g_check'] = sp.sstr(g) == sp.sstr(5 + 12*t + 15*t**2 + 4*t**3)

pts = [R(1,20), R(1,10), R(3,20)]
vals = [sp.simplify(g.subs(t, p)) for p in pts]
out['f_values'] = [sp.sstr(v) for v in vals]
out['f_values_expected'] = ['2819/500', '3177/500', '7151/1000']
out['f_values_match'] = [sp.sstr(v) for v in vals] == out['f_values_expected']

L, U, Rr = R(15409, 10000), R(15877, 10000), R(16352, 10000)
fa, fc, fb = [sp.Rational(v) for v in vals]
out['bound_left'] = bool(L**4 < fa)
out['bound_mid'] = bool(fc < U**4)
out['bound_right'] = bool(Rr**4 < fb)
out['midpoint_strict'] = bool(U < (L + Rr)/2)
out['all_bounds_exact'] = all([out['bound_left'], out['bound_mid'], out['bound_right'], out['midpoint_strict']])
out['gap'] = sp.sstr((L + Rr)/2 - U)
out['violation_chain_valid'] = all([L**4 < fa, fc < U**4, U < (L + Rr)/2, L > 0, Rr > 0])
out['numeric'] = [float(sp.N(fa**R(1,4))), float(sp.N(fc**R(1,4))), float(sp.N(fb**R(1,4)))]

Cg = sp.expand(4*g*sp.diff(g, t, 2) - 3*sp.diff(g, t)**2)
out['Cg'] = sp.sstr(Cg)
out['Cg_at_0'] = sp.sstr(Cg.subs(t, 0))

E = sp.expand(P*sp.diff(P, x, 2) - sp.Rational(3,4)*sp.diff(P, x)**2)
out['conj3_expr'] = sp.sstr(sp.factor(4*E))
out['conj3_leq0_all_R'] = sp.sstr(sp.expand(4*E + 144*(x**2 - 1)**2)) == '0'

print(json.dumps(out, indent=1))
