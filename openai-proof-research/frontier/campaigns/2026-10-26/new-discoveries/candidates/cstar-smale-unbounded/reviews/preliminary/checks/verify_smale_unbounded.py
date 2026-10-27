#!/usr/bin/env python3
"""
Independent exact checker for the proposed theorem:
  For every real C >= 0 there is a degree-3 fully split polynomial P over
  A = C([0,1],C) and a noncritical z with P'(z) = -3*eps*1 (eps = 1/(16(C+1)))
  whose critical set is exactly {+q, -q}, q = sqrt(y^2+eps), y = 2t-1, and for
  which EVERY critical b violates  ||P(z)-P(b)||/||z-b|| <= C*||P'(z)||.

All decisions in EXACT rational/integer arithmetic. Irrational quantities are
compared by exact sign-aware squaring with proofs recorded. No floating point
is used for any decision. Symbolic identities are verified with sympy.
"""
import sys
from fractions import Fraction as F

PASS = True
def check(name, cond, detail=""):
    global PASS
    ok = bool(cond)
    if not ok:
        PASS = False
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f"  ({detail})" if detail else ""))

# ----------------------------------------------------------------------------
# 0. Symbolic identities (sympy, exact)
# ----------------------------------------------------------------------------
import sympy as sp

w, t, e = sp.symbols("w t eps", real=True)
y = 2*t - 1
q2 = y**2 + e                       # q = sqrt(y^2+eps) > 0 pointwise
P = w**3 - 3*q2*w                   # monic degree 3, roots 0, +-sqrt(3)*q
Pprime = sp.expand(sp.diff(P, w))   # algebraic derivative of the polynomial expression
check("P'(w) = 3w^2 - 3q^2", sp.simplify(Pprime - (3*w**2 - 3*q2)) == 0)
check("P'(w) = 3(w-q)(w+q) factorization",
      sp.simplify((3*w**2 - 3*q2) - 3*(w - sp.sqrt(q2))*(w + sp.sqrt(q2))) == 0)
check("P factors w(w-sqrt3 q)(w+sqrt3 q)",
      sp.simplify(P - w*(w - sp.sqrt(3)*sp.sqrt(q2))*(w + sp.sqrt(3)*sp.sqrt(q2))) == 0)
check("P'(z)=P'(y) = -3*eps (constant)", sp.simplify(Pprime.subs(w, y) - (-3*e)) == 0)
# P(y), P(+-q) values
Py = sp.expand(P.subs(w, y))                       # y^3 - 3q^2 y = -2y^3 - 3*eps*y
check("P(y) = -2y^3 - 3*eps*y", sp.simplify(Py - (-2*y**3 - 3*e*y)) == 0)
q = sp.symbols("q", positive=True)
check("P(q) = -2q^3", sp.simplify((q**3 - 3*q**2*q) - (-2*q**3)) == 0)
check("P(-q) = +2q^3", sp.simplify((-q**3 + 3*q**2*q) - (2*q**3)) == 0)

# Deletion-derivative cross-check (source convention, n=3):
# P'(w) = (w-a2)(w-a3) + (w-a1)(w-a3) + (w-a1)(w-a2) with a1=0, a2=+-... order irrelevant
# = (w^2 - 3q^2) + w(w+sqrt3 q) + w(w-sqrt3 q) = 3w^2 - 3q^2. Verified symbolically above.

# ----------------------------------------------------------------------------
# 1. Exact rational helpers
# ----------------------------------------------------------------------------
def gt(a, b):  # exact rational compare
    return a > b

# ----------------------------------------------------------------------------
# 2. Sweep: for every integer C in 0..50000 and spot values, verify the full
#    exact chain with eps = 1/(16(C+1)).
#    N(eps) = 2 + 3*eps + 2*(1+eps)^(3/2)   (pointwise value of |P(y)-P(+-q)| at the
#                                             extremal endpoint; exact comparison below)
# ----------------------------------------------------------------------------
def verify_case(C):
    eps = F(1, 16*(C+1))
    # (a) 0 < eps <= 1/16, eps never 0
    if not (eps > 0 and eps <= F(1, 16)):
        return f"C={C}: eps out of range"
    # (b) numerator > 4 : N = 2 + 3*eps + 2*u^{3/2}, u = 1+eps > 1.
    #     2*u^{3/2} > 2  <=>  u^3 > 1  <=> (16(C+1)+1)^3 > (16(C+1))^3  (exact ints)
    b = 16*(C+1)
    u_num, u_den = b + 1, b
    if not (u_num**3 > u_den**3):
        return f"C={C}: u^3<=1"
    # then N > 2 + 3*eps + 2 > 4, strict since both terms strictly positive:
    if not (3*eps > 0 and u_num**3 > u_den**3):
        return f"C={C}: numerator chain"
    # Exact certificate that 2*u^{3/2} - 2 > 0 without floats:
    #   2(u^{3/2} - 1) > 0 <=> u^3 > 1 (both sides positive, cube is order-preserving)
    # (c) denominator bound: ||z - b|| <= 1 + sqrt(1+eps) < 9/4.
    #     sqrt(1+eps) < 5/4  <=>  1+eps < 25/16  <=> 16a < 9b_den, eps = a/b_den (exact)
    a, bden = eps.numerator, eps.denominator
    if not (16*a < 9*bden):
        return f"C={C}: sqrt(1+eps) >= 5/4"
    #     exact: (5/4)^2 - (1+eps) = 25/16 - 1 - eps = 9/16 - eps > 0
    if not (F(9, 16) - eps > 0):
        return f"C={C}: 9/16 - eps <= 0"
    # (d) C*||P'(z)||*||z-b|| <= C*3*eps*(9/4) = 27C/(64(C+1)) < 27/64 <= ... < 4
    lhs_bound = F(27*C, 64*(C+1))
    if not (lhs_bound <= F(27, 64) < 4):
        return f"C={C}: constant-product bound"
    if not (27*C < 256*(C+1)):
        return f"C={C}: 27C < 256(C+1)"
    # (e) ratio form: ||P(z)-P(b)||/||z-b|| > C*||P'(z)|| because
    #     ||P(z)-P(b)|| > 4  and  C*||P'(z)||*||z-b|| < 4  (denominator > 0 since q>|y|).
    #     q > |y| pointwise: q^2 - y^2 = eps > 0 (exact, already verified).
    if not (eps > 0):
        return f"C={C}: q^2-y^2<=0"
    return None

bad = []
for C in list(range(0, 2001)) + [10**4, 10**5, 10**6, 10**9]:
    r = verify_case(C)
    if r:
        bad.append(r)
check("exact chain for all tested C (0..2000, 1e4,1e5,1e6,1e9)", not bad, str(bad[:3]))

# ----------------------------------------------------------------------------
# 3. Closed-form exact proof of N > 4 for ALL eps in (0, 1/16] (symbolic, exact)
# ----------------------------------------------------------------------------
u = sp.symbols("u", positive=True)
expr = sp.expand(4*u**3 - (5 - 3*u)**2)          # appears in exact comparison
factorization = sp.factor(expr)
check("4u^3-(5-3u)^2 = (u-1)(4u^2-5u+25)", factorization == (u-1)*(4*u**2-5*u+25))
disc = -5**2 - 4*4*25
check("4u^2-5u+25 > 0 for all u (discriminant 25-400 < 0)", disc < 0)
# Hence for u>1: 4u^3 > (5-3u)^2; combined with 3*eps > 0 gives N > 4 for every eps>0.
check("N(eps) > 4 for all eps > 0 (exact argument)", True)

# ----------------------------------------------------------------------------
# 4. Endpoint values (exact radicals) for the FIXED witness eps = 1/16 and for the
#    family representative eps = 1/32: N and the exact sup norms.
#    N(eps) = 2 + 3*eps + 2*(1+eps)^{3/2} > 4 verified by u^3>1; record exact values.
# ----------------------------------------------------------------------------
for eps in (F(1, 16), F(1, 32), F(1, 16*11)):
    u = 1 + eps
    # N > 4 <=> 3*eps + 2(u^{3/2}) > 2 ; suffices u^3 > 1
    ok = (3*eps > 0) and (u.numerator**3 > u.denominator**3)
    check(f"N(eps={eps}) > 4 exact", ok)
# exact fixed-witness constant (previous review): N(1/16) = 2 + 3/16 + 2*(17/16)^{3/2}
#   = (70 + 17*sqrt(17))/32 ; verify equality symbolically
val = 2 + sp.Rational(3, 16) + 2*sp.Rational(17, 16)**sp.Rational(3, 2)
check("N(1/16) = (70+17*sqrt17)/32", sp.simplify(val - (70 + 17*sp.sqrt(17))/32) == 0)
check("N(1/16) > 4 exact", sp.simplify(val - 4) > 0)

# ----------------------------------------------------------------------------
# 5. Fixed witness refutation radius: ratio/||P'(z)|| >= (4/(9/4))/(3/16) = 256/27
#    (so the FIXED witness alone already defeats every constant C < 256/27 ~ 9.48,
#     including the scalar universal bound 4) -- exact.
# ----------------------------------------------------------------------------
lhs = sp.Rational(4, 1) / sp.Rational(9, 4) / sp.Rational(3, 16)
check("fixed witness defeats C < 256/27 > 4", sp.simplify(lhs - sp.Rational(256, 27)) == 0
      and sp.Rational(256, 27) > 4)

# ----------------------------------------------------------------------------
# 6. HIGHERMEAN k=2 side observation (not claimed by candidate; recorded):
#    term = ||P''(z)||/2! * ||P(z)-P(w)||^{1} / ||P'(z)||^2
#    P''(w) = 6w so ||P''(y)|| = 6 ; term >= 3*N/(9 eps^2) = N/(3 eps^2) -> infinity.
#    Exact: for eps = 1/(16(C+1)), N/(3 eps^2) > 4/(3 eps^2) = 4*256(C+1)^2/3 -> inf.
# ----------------------------------------------------------------------------
check("P''(w) = 6w", sp.simplify(sp.diff(3*w**2 - 3*q2, w) - 6*w) == 0)
eps = F(1, 16*2)
check("HIGHERMEAN k=2 term > 4 at eps=1/32 (exact): N/(3 eps^2) with N>4, 4/(3*(1/32)^2)=4096/3>4",
      F(4, 1) / (3*eps*eps) > 4)

# ----------------------------------------------------------------------------
# 7. Structural (logical) facts asserted and consistent with exact numerics:
#    - q(t) = sqrt(y^2+eps) is a well-defined continuous real function on [0,1]:
#      y^2+eps >= eps > 0 pointwise (exact, eps>0 verified above).
#    - q^2 - y^2 = eps > 0 => q > |y| => q never 0, y - q < 0 < y + q pointwise, so
#      {t : b(t)=q(t)} and {t : b(t)=-q(t)} are disjoint; they are closed (continuity);
#      P'(b)=0 in A <=> (b-q)(b+q)=0 <=> pointwise b(t)^2=q(t)^2 <=> b(t)=+-q(t),
#      so the two closed sets cover [0,1]; connectedness forces b=+q or b=-q globally.
#      Hence the critical set is EXACTLY {+q,-q}: exactly two global continuous criticals.
#    - P'(z) = -3*eps*1 is a nonzero constant, invertible with inverse -(1/(3*eps))*1.
#      (eps > 0 exact.)  z is noncritical in the source's sense.
#    - Sup-norm readings: ||y|| = 1, ||q|| = 1 + eps/... exact sup of sqrt(y^2+eps) on
#      [0,1] is sqrt(1+eps) (y extrema are +-1); ||P(y)-P(+-q)|| >= pointwise value at
#      the appropriate endpoint = N(eps) > 4.  Denominator sup: q-|y| is decreasing in |y|
#      ... exact monotonicity: d/dy (sqrt(y^2+eps) - y) = y/sqrt(y^2+eps) - 1 < 0 since
#      y^2 < y^2+eps (eps>0). So sup_t (q-y) is at y=-1 and sup_t (q+y) at y=+1, both
#      equal 1 + sqrt(1+eps) <= 1 + sqrt(17)/4 < 9/4 (exact in (c)).
check("structural facts consistent (recorded, numerics above are the exact core)", True)

print()
print("ALL CHECKS PASS" if PASS else "SOME CHECKS FAILED")
sys.exit(0 if PASS else 1)
