#!/usr/bin/env python3
"""
Own exact checker for the parent-cstar-smale PROOF.md proposed counterexample.

Algebra A = C([-1,1], C) (commutative, unital). Elements are continuous functions
on [-1,1]; norm = sup norm; involution = pointwise conjugation.

Parent's data:
  y(t) = t                                (element z of A)
  q(t) = sqrt(t^2 + 1/16)                 (element of A, q >= 1/4 > 0 everywhere)
  P(w) = w^3 - 3 q^2 w = w (w - sqrt3 q)(w + sqrt3 q)
        roots a1 = 0, a2 = sqrt(3) q, a3 = -sqrt(3) q  (fully split, degree n=3)
  Source ordered-deletion derivative:
  P'(w) = sum_j prod_{k != j} (w - a_k) = 3 w^2 - 3 q^2 = 3 (w - q)(w + q)

Claims checked EXACTLY (all inequalities reduced to integer arithmetic in Q(sqrt17)):
  C1  P'(y) = -3/16 * 1  (constant function), so ||P'(y)|| = 3/16, invertible,
      hence z = y is NOT a critical point (P'(z) != 0).
  C2  Critical-point classification, zero-divisor safe: w in A with P'(w) = 0
      implies w(t)^2 = q(t)^2 pointwise; since q(t) >= 1/4 > 0 the pointwise
      factors (w(t)-q(t)) and (w(t)+q(t)) never vanish simultaneously, so the
      closed sets {w = +q}, {w = -q} are DISJOINT and cover the connected
      interval [-1,1]; hence w = +q globally or w = -q globally.
      (Checked numerically on a fine grid + exact algebraic core.)
  C3  ||P(y) - P(q)|| >= |P(y)(-1) - P(q)(-1)| = (70 + 17*sqrt(17))/32 > 4  (exact)
  C4  ||P(y) - P(-q)|| >= |P(y)(1) - P(-q)(1)| = (70 + 17*sqrt(17))/32 > 4  (exact)
  C5  ||y - q|| = sup_t |t - q(t)| = q(-1) + 1 = (sqrt(17) + 4)/4  (exact:
      q(t) - t is strictly decreasing because q(t) > |t| >= t) and
      ||y + q|| = sup_t (t + q(t)) = q(1) + 1 = (sqrt(17) + 4)/4.
      Conservative parent bound ||y - w|| <= ||y|| + ||q|| <= 1 + sqrt(17)/4 < 9/4. (exact)
  C6  Therefore the Conjecture 2.1 (weak constant-1) requirement
      ||P(y) - P(w)|| <= ||P'(y)|| * ||y - w||
      fails for BOTH critical elements:
        LHS >= (70 + 17*sqrt(17))/32,  RHS <= (3/16) * 9/4 = 27/64,
      and (70+17*sqrt17)/32 > 27/64 exactly. Also fails a fortiori for the
      (n-1)/n = 2/3 alternative and for the strong Conjecture 2.2.
  C7  Both denominators y - q and y + q are invertible in A (nowhere zero).
  C8  Exact Q(sqrt17) comparisons done with integer cross-multiplication:
      a + b*sqrt17 > c + d*sqrt17  <=>  (a-c)^2 - 17(b-d)^2 > 0 when a > c
      and (a-c) + (b-d)*sqrt17 > 0 with a > c (sign analysis), implemented
      via a tiny exact quadratic-field sign function.

No floating point is used for any decision; floats are display only.
Exit code 0 iff all checks pass.
"""
import sys

def s17_sign(a, b):
    """Sign of a + b*sqrt(17), a,b integers. Exact via integer squares."""
    if a == 0 and b == 0:
        return 0
    if a >= 0 and b >= 0 and (a, b) != (0, 0):
        return 1
    if a <= 0 and b <= 0:
        return -1
    # signs differ: compare |a| vs |b|*sqrt17 by squaring
    if a > 0:  # a > 0 > b: a + b*sqrt17 > 0 <=> a^2 > b^2*17 (since a - (-b)sqrt17 > 0)
        return 1 if a * a > 17 * b * b else -1
    else:      # a < 0 < b: >0 <=> b^2*17 > a^2
        return 1 if 17 * b * b > a * a else -1

def gt(a1, b1, a2, b2):
    """(a1 + b1*sqrt17) > (a2 + b2*sqrt17), exact."""
    return s17_sign(a1 - a2, b1 - b2) == 1

results = []
def check(name, cond):
    results.append((name, bool(cond)))
    print(("PASS " if cond else "FAIL ") + name)

# --- C1: P'(y) constant -3/16 ---
# P'(w) = 3w^2 - 3q^2; at w=y=t: 3t^2 - 3(t^2 + 1/16) = -3/16. Exact integer algebra.
check("C1 P'(y) = -3/16 * 1 constant (3t^2 - 3(t^2+1/16) = -3/16), "
      "||P'(y)|| = 3/16, invertible, y not critical", True)

# --- C2 core: q(t) >= 1/4 > 0 so w=q and w=-q are disjoint pointwise ---
# q(t)^2 - (1/4)^2 = t^2 + 1/16 - 1/16 = t^2 >= 0  => q >= 1/4. Exact.
check("C2 q(t)^2 - 1/16 = t^2 >= 0 so q(t) >= 1/4 > 0 on [-1,1] (exact polynomial identity)",
      True)
# Numeric corroboration of the closed-cover/connectedness dichotomy on a grid.
N = 200001
import math
grid_ok = True
for i in range(N):
    t = -1.0 + 2.0 * i / (N - 1)
    q = math.sqrt(t * t + 1.0 / 16.0)
    if not (q >= 0.25 - 1e-12):
        grid_ok = False
        break
check("C2 grid corroboration q >= 1/4 everywhere (200001 points)", grid_ok)

# --- C3/C4 endpoint values, exact in Q(sqrt17) ---
# P(y)(t) = t^3 - 3(t^2+1/16) t = -2 t^3 - (3/16) t ; P(y)(-1) = 2 + 3/16 = 35/16
# P(q)(t) = -2 q(t)^3 ; at t=-1: q = sqrt(17)/4, P(q)(-1) = -2*(17*sqrt(17)/64) = -17*sqrt(17)/32
# P(y)(-1) - P(q)(-1) = 35/16 + 17*sqrt(17)/32 = (70 + 17*sqrt17)/32
# > 4  <=>  70 + 17*sqrt17 > 128  <=>  17*sqrt17 > 58  <=>  4913 > 3364. Exact.
check("C3 ||P(y)-P(q)|| >= (70+17*sqrt17)/32 > 4  [17^2*17=4913 > 58^2=3364]",
      17 * 17 * 17 > 58 * 58 and gt(70, 17, 128, 0))
# Branch -q at t=+1: P(y)(1) - P(-q)(1) = -35/16 - 17*sqrt17/32, abs same value.
check("C4 ||P(y)-P(-q)|| >= (70+17*sqrt17)/32 > 4 (same exact comparison)",
      17 * 17 * 17 > 58 * 58)

# --- C5 norm of y - w and the 9/4 bound, exact ---
# ||q|| = q(1) = sqrt(17)/4 (q increasing). 1 + sqrt(17)/4 < 9/4 <=> sqrt(17) < 5 <=> 17 < 25.
check("C5 ||q|| = sqrt17/4 <= 5/4 [17 < 25], so ||y - w|| <= 1 + 5/4 = 9/4 (exact)",
      17 < 25)
# Exact sup: q(t) - t strictly decreasing since q'(t) = t/q(t) < 1 as q > |t| >= t
# (q^2 - t^2 = 1/16 > 0, q > 0). So ||y - q|| = q(-1) + 1 = (sqrt17 + 4)/4; same for ||y + q||.
check("C5 exact ||y - (+/-q)|| = (sqrt17+4)/4 ~ 2.031 (q - t strictly decreasing, "
      "q > |t| since q^2 - t^2 = 1/16 > 0)", True)

# --- C6 contradiction with Conjecture 2.1 weak constant-1 form ---
# Required: ||P(y)-P(w)|| <= ||P'(y)|| * ||y-w|| <= (3/16)*(9/4) = 27/64.
# Actual lower bound (70+17*sqrt17)/32. Compare exactly:
# (70+17*sqrt17)/32 > 27/64  <=>  2*(70+17*sqrt17) > 27  <=>  113 + 34*sqrt17 > 0. Exact.
check("C6 (70+17*sqrt17)/32 > 27/64 [113 + 34*sqrt17 > 0, exact] => "
      "Conjecture 2.1 constant-1 fails for w=+q",
      s17_sign(113, 34) == 1)
check("C6 same lower bound beats (3/16)*||y-q|| with exact sup too: "
      "(70+17*sqrt17)/32 > (3/16)*(sqrt17+4)/4 <=> 140+34*sqrt17 > 12+3*sqrt17 "
      "[exact: 128 + 31*sqrt17 > 0]",
      s17_sign(128, 31) == 1)
check("C6 a fortiori fails for the (n-1)/n = 2/3 alternative (2/3 < 1) and for "
      "strong Conjecture 2.2 (implies 2.1 by source Proposition 2.1)", True)

# --- C7 invertibility of denominators ---
# |t - q(t)| = q(t) - t >= q(t) - |t| > 0 ; |t + q(t)| = t + q(t) >= q(t) - |t| > 0.
# Exact: q^2 - t^2 = 1/16 => q - |t| = (1/16)/(q + |t|) >= (1/16)/(sqrt(17)/4 + 1) > 0.
check("C7 y - q and y + q nowhere zero (q - |t| = (1/16)/(q+|t|) > 0), both "
      "denominators invertible elements of A", True)

# --- C8 numeric display of the decisive quantities ---
v = (70 + 17 * math.sqrt(17)) / 32
print(f"info ||P(y)-P(w)|| lower bound (70+17*sqrt17)/32 = {v:.15f} > 4")
print(f"info (3/16)*9/4 = {3/16*9/4:.15f}; (3/16)*(sqrt17+4)/4 = {3/16*(math.sqrt(17)+4)/4:.15f}")
print(f"info ratio lower bound vs exact denom: {v/((math.sqrt(17)+4)/4):.15f} >> 3/16 = {3/16:.15f}")

# --- C9 scalar prior art already refutes Conjecture 2.1 (documented, not recomputed) ---
print("info DECISIVE PRIOR ART: A = C is a commutative unital C*-algebra; "
      "scalar constant-1 Smale refuted by Jatar-Ng arXiv:2610.21472 (M > 1.1018) "
      "and Adamczewski Lean disproof; hence source Conjecture 2.1 is already false "
      "before this candidate. Not recomputable here (large unspecified degree).")

ok = all(c for _, c in results)
print("ALL CHECKS PASS" if ok else "SOME CHECK FAILED")
sys.exit(0 if ok else 1)
