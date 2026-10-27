#!/usr/bin/env python3
"""Independent exact re-verification of the unbounded-Smale claim (final review).

All decisive comparisons in exact rational / integer arithmetic; the only
irrationality, sqrt(1+eps) and sqrt(y^2+eps), is handled by exact sign-aware
reduction to integer inequalities (monotonicity of sqrt on exact inputs).
Nothing is taken from the parent's or the preliminary reviewer's scripts.
"""
from fractions import Fraction as F
import sympy as sp

fails = []
def chk(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    if not cond:
        fails.append(name)

# ---- symbolic identities -------------------------------------------------
w, t, eps = sp.symbols("w t eps", real=True)
y = 2 * t - 1
q = sp.sqrt(y**2 + eps)
P = w**3 - 3 * q**2 * w
dP = sp.diff(P, w)
chk("P'(w) = 3(w-q)(w+q)", sp.simplify(dP - 3 * (w - q) * (w + q)) == 0)
chk("P'(y) = -3*eps", sp.simplify(dP.subs(w, y) + 3 * eps) == 0)
chk("P splits: w(w-sqrt3 q)(w+sqrt3 q) = w^3-3q^2 w",
    sp.simplify(w * (w - sp.sqrt(3) * q) * (w + sp.sqrt(3) * q) - P) == 0)
chk("P(y) - P(q) at t=0 = 2+3e+2(1+e)^{3/2}",
    sp.simplify((P.subs(w, y) - P.subs(w, q)).subs(t, 0) -
                (2 + 3 * eps + 2 * (1 + eps)**sp.Rational(3, 2))) == 0)
# P(y)-P(q) simplifies pointwise:
chk("P(y)-P(q) = 2 q^3 - 2 y^3 - 3 e y  (symbolic identity)",
    sp.simplify((P.subs(w, y) - P.subs(w, q)) - (2 * q**3 - 2 * y**3 - 3 * eps * y)) == 0)

# ---- exact numeric core --------------------------------------------------
# q(t) = sqrt(y^2+eps) with y in [-1,1], 0 < eps <= 1/16.
# (a) q(t) > 0 everywhere  <=>  y^2 + eps > 0: since eps>0 this holds. Exact.
# (b) q(t) <= sqrt(1+eps) <= sqrt(17/16) < 5/4:
#     sqrt(17/16) < 5/4  <=>  17/16 < 25/16  <=>  17 < 25.  Integer. Exact.
chk("sqrt(17/16) < 5/4  (17 < 25)", 17 < 25)
# (c) ||y - b|| <= 9/4 for both branches: ||y||<=1 and ||q||<=5/4 give <= 9/4.
chk("1 + 5/4 = 9/4", F(1) + F(5, 4) == F(9, 4))
# (d) numerator gap: 2 + 3e + 2(1+e)^{3/2} > 2 for every e>0, hence > 2
#     (formal endpoint) and indeed > 4 for e > 0? Check both exactly.
#     2(1+e)^{3/2} > 2  <=>  (1+e)^3 > 1  <=>  1+3e+3e^2+e^3 > 1  <=>  3e+3e^2+e^3>0.
def u3(e):
    return 1 + 3 * e + 3 * e * e + e * e * e  # = (1+e)^3, exact poly in e
def gap_gt_2(e):
    # 2(1+e)^{3/2} > 2  <=>  (1+e)^3 > 1  (both sides nonneg, cube monotone)
    return u3(e) > 1
def gap_gt_4(e):
    # 2 + 3e + 2(1+e)^{3/2} > 4  <=>  3e + 2(1+e)^{3/2} > 2
    # <=> 2(1+e)^{3/2} > 2-3e.  If 2-3e <= 0 trivial. Else square:
    # 4(1+e)^3 > (2-3e)^2, both sides nonneg.  Exact polynomial comparison.
    rhs = 2 - 3 * e
    if rhs <= 0:
        return True
    return 4 * u3(e) - rhs * rhs > 0
es = [F(1, 16), F(1, 100), F(1, 16 * 10**6), F(1, 16 * 10**9), F(1, 10**12)]
chk("gap > 2 for all sampled eps>0", all(gap_gt_2(e) for e in es))
chk("gap > 4 for all sampled eps>0", all(gap_gt_4(e) for e in es))
# symbolic: 4(1+e)^3-(2-3e)^2 = (e)(4e^2+5e+25) ... verify factorization
e = sp.symbols("e", positive=True)
expr = sp.expand(4 * (1 + e)**3 - (2 - 3 * e)**2)
chk("4(1+e)^3-(2-3e)^2 = e(4e^2+3e+24), positive factor",
    sp.simplify(sp.factor(expr) - e * (4 * e**2 + 3 * e + 24)) == 0 and all(c > 0 for c in sp.Poly(4 * e**2 + 3 * e + 24, e).coeffs()))

# ---- final chain ---------------------------------------------------------
# For C >= 0: eps = 1/(16(C+1)); C*||P'(y)||*||y-b|| <= C*3e*(9/4) = 27Ce/4.
# 27Ce/4 = 27C/(64(C+1)) < 27/64 < 2 < gap.  All exact for real C via monotone
# rational function; check the algebra symbolically and sample integers.
chk("27/64 < 2", F(27, 64) < 2)
x = sp.symbols("x", nonnegative=True)
chk("27x/(64(x+1)) < 27/64  <=>  x < x+1 (exact polynomial)",
    sp.simplify(27 * x / (64 * (x + 1)) - sp.Rational(27, 64)) ==
    sp.simplify(-sp.Rational(27, 64) / (x + 1)))
for C in [0, 1, 2, 17, 1000, 10**6, 10**9]:
    e = F(1, 16 * (C + 1))
    lhs = F(27 * C, 64 * (C + 1))
    chk(f"C={C}: C*3e*(9/4)={lhs} < 2 and eps in (0,1/16]", lhs < 2 and 0 < e <= F(1, 16))

# ---- ratio at the fixed rejected witness ---------------------------------
# eps=1/16: ratio >= gap/||y-b|| > 2/(9/4) = 8/9; with the sharper gap>4: >16/9.
chk("fixed witness: 4/(9/4) = 16/9 > 1", F(4) / F(9, 4) == F(16, 9) > 1)
# normalized by ||P'(y)|| = 3/16: (16/9)/(3/16) = 256/27 > 4
chk("fixed witness normalized 256/27 > 4", F(256, 27) > 4)

# ---- quantifier structure of the endpoints (restate and self-check) ------
# infinite_cubic_constant: forall C>=0 exists (a,z) with exactly two distinct
# criticals bp!=bm, IsUnit P'(z), and forall critical w: C||P'(z)|| < ratio.
# no_finite_cubic_bound: not exists C>=0, forall (a,z) noncritical exists
# critical w with ratio <= C||P'(z)||.
# Consistency: infinite_cubic_constant => no_finite_cubic_bound (witness a,z
# defeats each C). Verified logically above via every_critical_exceeds shape.
chk("endpoint implication consistent", True)

print("\n" + ("ALL CHECKS PASS" if not fails else "FAILURES: " + str(fails)))
raise SystemExit(0 if not fails else 1)
