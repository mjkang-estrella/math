#!/usr/bin/env python3
"""Exact finite checks of the coefficientwise identities used in proof.md.

Arithmetic is exact: Z[i] and Z[w] (w = exp(2 pi i/3)) are represented by
integer pairs. Every identity in proof.md that is asserted for all choices
of alphabet letters is checked here over the complete finite set of letters.
These are integrity controls for the written algebra; the general theorem is
the argument in proof.md, not these checks.  Writes JSON to stdout.
"""
import itertools, json, sys
from fractions import Fraction

# ---------- Z[i]: a + b i ----------
def gi_add(x, y): return (x[0] + y[0], x[1] + y[1])
def gi_sub(x, y): return (x[0] - y[0], x[1] - y[1])
def gi_mul(x, y): return (x[0]*y[0] - x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def gi_conj(x): return (x[0], -x[1])
def gi_div_exact(x, y):
    """x / y in Z[i] if exact, else None."""
    n = y[0]*y[0] + y[1]*y[1]
    num = gi_mul(x, gi_conj(y))
    if num[0] % n or num[1] % n: return None
    return (num[0] // n, num[1] // n)
GI_UNITS = [(1, 0), (0, 1), (-1, 0), (0, -1)]
PI = (1, 1)          # 1 + i
PIBAR = (1, -1)      # 1 - i

# ---------- Z[w]: a + b w, w^2 = -1 - w ----------
def ew_add(x, y): return (x[0] + y[0], x[1] + y[1])
def ew_sub(x, y): return (x[0] - y[0], x[1] - y[1])
def ew_mul(x, y):
    a, b = x; c, d = y
    # (a + b w)(c + d w) = ac + (ad + bc) w + bd w^2, w^2 = -1 - w
    return (a*c - b*d, a*d + b*c - b*d)
def ew_conj(x):
    a, b = x  # conj(w) = w^2 = -1 - w
    return (a - b, -b)
def ew_norm(x): return ew_mul(x, ew_conj(x))[0]
def ew_div_exact(x, y):
    n = ew_norm(y)
    num = ew_mul(x, ew_conj(y))
    if num[0] % n or num[1] % n: return None
    return (num[0] // n, num[1] // n)
ONE, W = (1, 0), (0, 1)
W2 = ew_mul(W, W)
MU3 = [ONE, W, W2]
LAM = ew_sub(ONE, W)  # 1 - w

results = {}
def record(name, ok, detail=None):
    results[name] = {"ok": bool(ok)} if detail is None else {"ok": bool(ok), "detail": detail}

# (a) units congruent to 1 mod (1+i); (1+i)(1-i) = 2
record("a_units_1_mod_pi", all(gi_div_exact(gi_sub(u, (1, 0)), PI) is not None for u in GI_UNITS))
record("a_pi_pibar_is_2", gi_mul(PI, PIBAR) == (2, 0))
# every coefficient of H0 + eta H1, eta = +-1, is divisible by 1+i
record("a_partial_eval_divisible",
       all(gi_div_exact(gi_add(u0, gi_mul((e, 0), u1)), PI) is not None
           for u0 in GI_UNITS for u1 in GI_UNITS for e in (1, -1)))
# d - c = -(1-i) H1 coefficientwise: ((u0 - u1) - (u0 + u1))/(1+i) = -(1-i) u1
record("a_difference_identity",
       all(gi_div_exact(gi_sub(gi_sub(u0, u1), gi_add(u0, u1)), PI)
           == gi_mul((-1, 0), gi_mul(PIBAR, u1)) for u0 in GI_UNITS for u1 in GI_UNITS))
# elementary parity: a sum of N units is 0 only if N is even (checked for N <= 6)
def gi_sums_zero(N):
    return any(sum(u[0] for u in c) == 0 and sum(u[1] for u in c) == 0
               for c in itertools.product(GI_UNITS, repeat=N))
record("a_odd_unit_sums_nonzero", all(not gi_sums_zero(N) for N in (1, 3, 5)))

# (b) cube roots congruent to 1 mod lambda; lambda * conj(lambda) = 3
record("b_mu3_1_mod_lambda", all(ew_div_exact(ew_sub(u, ONE), LAM) is not None for u in MU3))
record("b_lambda_norm_3", ew_norm(LAM) == 3)
record("b_lambda_sq_is_minus3w", ew_mul(LAM, LAM) == ew_mul((-3, 0), W))
# coefficient sums u0 + eta u1 + eta^2 u2 are divisible by lambda
record("b_partial_eval_divisible",
       all(ew_div_exact(ew_add(ew_add(u0, ew_mul(e, u1)), ew_mul(ew_mul(e, e), u2)), LAM) is not None
           for u0 in MU3 for u1 in MU3 for u2 in MU3 for e in MU3))
# (w - 1)/lambda = -1, (w^2 - 1)/lambda = w^2
record("b_quotients", ew_div_exact(ew_sub(W, ONE), LAM) == (-1, 0)
       and ew_div_exact(ew_sub(W2, ONE), LAM) == W2)
def ev(us, e):  # u0 + e u1 + e^2 u2
    return ew_add(ew_add(us[0], ew_mul(e, us[1])), ew_mul(ew_mul(e, e), us[2]))
ok_x = ok_m = ok_sum = ok_cong = True
for us in itertools.product(MU3, repeat=3):
    x1 = ew_div_exact(ev(us, ONE), LAM)
    xw = ew_div_exact(ev(us, W), LAM)
    xw2 = ew_div_exact(ev(us, W2), LAM)
    if None in (x1, xw, xw2): ok_x = False; continue
    # x_w - x_1 = -u1 + w^2 u2 ;  x_{w^2} - x_1 = w^2 u1 - u2
    if ew_sub(xw, x1) != ew_add(ew_mul((-1, 0), us[1]), ew_mul(W2, us[2])): ok_x = False
    if ew_sub(xw2, x1) != ew_sub(ew_mul(W2, us[1]), us[2]): ok_x = False
    M = ew_div_exact(ew_sub(xw, x1), LAM); Mp = ew_div_exact(ew_sub(xw2, x1), LAM)
    if M is None or Mp is None: ok_m = False; continue
    if ew_add(M, Mp) != ew_mul(W2, ew_add(us[1], us[2])): ok_sum = False
    # M + M' = -1 (mod lambda)
    if ew_div_exact(ew_add(ew_add(M, Mp), ONE), LAM) is None: ok_cong = False
record("b_difference_identities", ok_x)
record("b_divisible_by_lambda", ok_m)
record("b_first_order_sum_identity", ok_sum)
record("b_first_order_sum_congruent_minus_one", ok_cong)
def ew_sums_zero(N):
    return any((sum(u[0] for u in c), sum(u[1] for u in c)) == (0, 0)
               for c in itertools.product(MU3, repeat=N))
record("b_nonmultiple_of_3_cube_sums_nonzero", all(not ew_sums_zero(N) for N in (1, 2, 4, 5)))

# ---------- barrier examples (group-ring identities, exact) ----------
def gr_mul(a, b, n, mul, add, zero):
    out = [zero] * n
    for j, x in enumerate(a):
        for k, y in enumerate(b):
            out[(j + k) % n] = add(out[(j + k) % n], mul(x, y))
    return out
def gr_star(a, n, conj):
    return [conj(a[(-k) % n]) for k in range(n)]
# Example 1: x = -1 + g + g^2 + g^4 in Z[C_7] has x x^* = 4.
x7 = [(-1, 0), (1, 0), (1, 0), (0, 0), (1, 0), (0, 0), (0, 0)]
p7 = gr_mul(x7, gr_star(x7, 7, gi_conj), 7, gi_mul, gi_add, (0, 0))
record("barrier_C7_norm_4", p7 == [(4, 0)] + [(0, 0)] * 6)
# Example 2: x = (-9 + 12 i) + 2 J in Z[i][C_9] has x x^* = 225, and
# x(1)/x(rho) = (9+12i)/(-9+12i) = (7-24i)/25 is not an algebraic integer.
x9 = [gi_add((-9, 12), (2, 0))] + [(2, 0)] * 8
p9 = gr_mul(x9, gr_star(x9, 9, gi_conj), 9, gi_mul, gi_add, (0, 0))
ratio = gi_div_exact((9, 12), (-9, 12))
num = gi_mul((9, 12), gi_conj((-9, 12)))
fr = (Fraction(num[0], 225), Fraction(num[1], 225))
record("barrier_C9_norm_225", p9 == [(225, 0)] + [(0, 0)] * 8,
       {"x(1)": [9, 12], "x(rho)": [-9, 12], "ratio_exact_in_Z[i]": ratio is not None,
        "ratio": [str(fr[0]), str(fr[1])]})

# ---------- route-limit checks (why the method stops) ----------
# mu_4 with a C_4 factor: a sum of four letters need not be divisible by 2,
# so h_eta/2 is not automatically integral.
record("limit_mu4_C4_sum_not_div_2",
       any(gi_div_exact(gi_add(gi_add(a, b), gi_add(c, d)), (2, 0)) is None
           for a in GI_UNITS for b in GI_UNITS for c in GI_UNITS for d in GI_UNITS))
# mu_3 with a C_9 factor: a sum of nine cube roots need not be divisible by 3.
s9 = ew_add((8, 0), W)  # eight 1's and one w
record("limit_mu3_C9_sum_not_div_3", ew_div_exact(s9, (3, 0)) is None)
# mu_4, C_4 factor, first-order quantities of the three residue-one-type
# differences depend mod (1+i) only on whether u1/u3 is +-1 or +-i.
def gi_mod_pi(x):  # residue of x in Z[i]/(1+i) = F_2
    return (x[0] + x[1]) % 2
def h_eval(us, e):
    acc = (0, 0); ep = (1, 0)
    for u in us:
        acc = gi_add(acc, gi_mul(ep, u)); ep = gi_mul(ep, e)
    return acc
ok = True
for us in itertools.product(GI_UNITS, repeat=4):
    typ = 1 if gi_mul(us[1], gi_conj(us[3])) in [(0, 1), (0, -1)] else 0
    d1 = gi_div_exact(gi_sub(h_eval(us, (-1, 0)), h_eval(us, (1, 0))), gi_mul((2, 0), PI))
    d2 = gi_div_exact(gi_sub(h_eval(us, (0, 1)), h_eval(us, (1, 0))), (2, 0))
    d3 = gi_div_exact(gi_sub(h_eval(us, (0, -1)), h_eval(us, (0, 1))), gi_mul((2, 0), PI))
    if None in (d1, d2, d3) or {gi_mod_pi(d1), gi_mod_pi(d2), gi_mod_pi(d3)} != {typ}:
        ok = False
record("limit_mu4_C4_first_order_terms_depend_only_on_u1_over_u3", ok)

json.dump({"all_ok": all(v["ok"] for v in results.values()), "checks": results},
          sys.stdout, indent=1, sort_keys=True)
print()
