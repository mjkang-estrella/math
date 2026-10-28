#!/usr/bin/env python3
"""Independent exact/diagnostic checks for the final review of the gamma-level
convexity candidate. Diagnostics only — no numeric evidence is treated as proof.
The proof itself was re-derived by hand (see review.md) and is certified by the
independent Lean replay."""
import json
import mpmath as mp
from fractions import Fraction

mp.mp.dps = 50
results = {}

# 1. Weight identity, exact over rationals:
#    (S+m)/X = A(s0+m)/x0 + B(s1+m)/x1 with A = a x0/X, B = b x1/X, X = a x0+b x1,
#    S = a s0 + b s1, a+b=1.
ok = True
import random
random.seed(7)
for _ in range(300):
    a = Fraction(random.randint(1, 99), 100)
    b = 1 - a
    x0 = Fraction(random.randint(1, 50), random.randint(1, 7))
    x1 = Fraction(random.randint(1, 50), random.randint(1, 7))
    s0 = x0 + Fraction(random.randint(1, 40), random.randint(1, 9))
    s1 = x1 + Fraction(random.randint(1, 40), random.randint(1, 9))
    X = a * x0 + b * x1
    S = a * s0 + b * s1
    for m in range(0, 4):
        lhs = (S + m) / X
        rhs = (a * x0 / X) * ((s0 + m) / x0) + (b * x1 / X) * ((s1 + m) / x1)
        if lhs != rhs:
            ok = False
results["weight_identity_exact_300"] = ok

# 2. Two-shift strictness, exact over rationals:
#    (s0)/x0 == s1/x1 and (s0+1)/x0 == (s1+1)/x1  ==>  x0 == x1.
ok = True
for _ in range(300):
    x0 = Fraction(random.randint(1, 99), random.randint(1, 9))
    x1 = Fraction(random.randint(1, 99), random.randint(1, 9))
    if x0 == x1:
        continue
    r = Fraction(random.randint(1, 99), random.randint(1, 9))
    s0, s1 = r * x0, r * x1  # forces m=0 equality
    # if also (s0+1)/x0 == (s1+1)/x1 then x0 == x1 must hold
    if (s0 + 1) / x0 == (s1 + 1) / x1:
        ok = False
results["two_shift_strictness_exact_300"] = ok

# 3. g'' formula vs high-precision finite difference.
def g(u):
    return -mp.log(1 - mp.power(u, -2))
def gpp(u):
    h = mp.mpf('1e-25')
    return (g(u + h) - 2 * g(u) + g(u - h)) / (h * h)
err = max(abs(gpp(u) - 2 * (3 * u**2 - 1) / (u**2 * (u**2 - 1)**2))
          for u in [mp.mpf('1.1'), mp.mpf('1.5'), mp.mpf('3'), mp.mpf('40')])
results["g_pp_formula_max_err"] = mp.nstr(err, 5)

# 4. Finite-cancellation identity:
#    sum_{m=0}^{n} g((s+m)/x) = logGammaSeq(s-x,n)+logGammaSeq(s+x,n)-2 logGammaSeq(s,n),
#    logGammaSeq a n = a log n + log n! - sum_{m=0}^{n} log(a+m).
def logGammaSeq(A, n):
    return A * mp.log(n) + mp.log(mp.factorial(n)) - mp.fsum([mp.log(A + m) for m in range(n + 1)])
ok = True
worst = 0
for (x, s, n) in [(mp.mpf('0.3'), mp.mpf('1.7'), 50), (mp.mpf('1'), mp.mpf('2'), 200),
                  (mp.mpf('2.5'), mp.mpf('10'), 300), (mp.mpf('0.1'), mp.mpf('0.15'), 100)]:
    lhs = mp.fsum([g((s + m) / x) for m in range(n + 1)])
    rhs = logGammaSeq(s - x, n) + logGammaSeq(s + x, n) - 2 * logGammaSeq(s, n)
    worst = max(worst, abs(lhs - rhs))
    if abs(lhs - rhs) > mp.mpf('1e-35'):
        ok = False
results["finite_cancellation_max_err"] = mp.nstr(worst, 5)
results["finite_cancellation_ok"] = ok

# 5. Full series identity F(x,s) = sum g((s+m)/x) within rigorous tail bound.
def F(x, s):
    return mp.log(mp.gamma(s - x)) + mp.log(mp.gamma(s + x)) - 2 * mp.log(mp.gamma(s))
def series(x, s, M):
    return mp.fsum([g((s + m) / x) for m in range(M)])
ok = True
for (x, s) in [(mp.mpf('0.3'), mp.mpf('1.7')), (mp.mpf('1'), mp.mpf('2')),
               (mp.mpf('2.5'), mp.mpf('10')), (mp.mpf('0.1'), mp.mpf('0.15'))]:
    M = 400000
    # rigorous-ish tail: each term <= x^2/((s+m)^2-x^2) <= x^2/((M)^2) summed
    tail_bound = x**2 / (M - 1)  # generous upper bound of sum_{m>=M} x^2/m^2 * (1/(1-...))
    diff = abs(F(x, s) - series(x, s, M))
    if diff > tail_bound:
        ok = False
    results[f"series_identity_x{x}_s{s}"] = {"diff": mp.nstr(diff, 5), "tail_bound": mp.nstr(tail_bound, 5)}
results["series_identity_ok"] = ok

# 6. c=2 level: h(1)=1 and h'(1)=2 (source anchors), convexity sample incl x<1.
def h(x, c=2):
    f = lambda y: mp.log(mp.gamma(y)) + mp.log(mp.gamma(y + 2 * x)) - 2 * mp.log(mp.gamma(y + x)) - mp.log(c)
    lo, hi = mp.mpf('1e-30'), mp.mpf('1')
    while f(lo) < 0:
        lo /= 2
    while f(hi) > 0:
        hi *= 2
    for _ in range(250):
        mid = (lo + hi) / 2
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2
results["h_of_1"] = mp.nstr(h(1), 12)
h05, h1, h15 = h(mp.mpf('0.5')), h(1), h(mp.mpf('1.5'))
results["h1_anchor_ok"] = abs(h(1) - 1) < mp.mpf('1e-25')
d1 = (h(1 + mp.mpf('1e-12')) - h(1 - mp.mpf('1e-12'))) / mp.mpf('2e-12')
results["h1_slope"] = mp.nstr(d1, 8)
xs = [mp.mpf(v) for v in ['0.05', '0.1', '0.2', '0.5', '1', '2', '5']]
hs = [h(x) for x in xs]
slopes = [(hs[i + 1] - hs[i]) / (xs[i + 1] - xs[i]) for i in range(len(xs) - 1)]
results["numeric_slopes_increasing"] = all(slopes[i] < slopes[i + 1] for i in range(len(slopes) - 1))
results["sample_heights"] = {str(float(x)): mp.nstr(y, 8) for x, y in zip(xs, hs)}

print(json.dumps(results, indent=2))
Path = json
with open(__file__.replace('ownchecks.py', 'ownchecks-result.json'), 'w') as f:
    json.dump(results, f, indent=2)
    f.write('\n')
