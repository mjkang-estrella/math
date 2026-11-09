#!/usr/bin/env python3
"""Independent adversarial math check for Schmidlin Conjecture 372858 review.

Own algorithm/path: sympy exact polynomial algebra + mpmath 60-digit sampling.
Checks:
 1. Literal identity mhat_{1/2}(x,a) = R(z)-E(z,a), z=x+1, a=alpha-1/2 (symbolic + numeric)
 2. Source bound rewrites to 1/(12(z+a)-k), k=12(e^{1/48}-1) in [1/4,1/2)
 3. rational_gap_identity: 1/(12(z+a)-1/4) - U(z) + a^2/(2z+a) = cubic/(2520 z^5 (a+2z)(48a+48z-1))
    with the exact coefficient table (A,B,C,F) and shifted positive coefficients
 4. upper_step_identity: U(z)-U(z+1)-H(z) = P(z)/(2520 z^5 (z+1)^5 (2z+1)^6), exact P
 5. U(z) upper-bounds logGamma error (classical check) and U(z)<=1/(12z) for z>=1
 6. Entropy bounds E>=0, E>=a^2/(2z+a)
 7. Full conjecture strict bound over dense grid incl. boundaries x=0, alpha=0,1/2,1 and a>=0 range
 8. GammaInterpolation sandwich numerics: R(n)-2/(n-1) <= R(n+r) <= R(n)+1/n
"""
import sympy as sp
import mpmath as mp
import json, sys

mp.mp.dps = 60
z, a, t, x, alpha = sp.symbols('z a t x alpha', real=True)

results = {}

def record(name, ok, detail=""):
    results[name] = {"pass": bool(ok), "detail": detail}
    print(("PASS " if ok else "FAIL ") + name + (" :: " + detail if detail else ""))

# ---------- definitions ----------
def U(zv):
    return 1/(12*zv) - 1/(360*zv**3) + 1/(1260*zv**5)

A = 120960*z**5
B = 120960*z**6 - 2520*z**5 - 10080*z**4 + 336*z**2 - 96
C = -20160*z**5 + 210*z**4 + 1008*z**3 - 7*z**2 - 288*z + 2
F = 420*z**5 + 672*z**4 - 14*z**3 - 192*z**2 + 4*z

# ---------- 3. rational gap identity ----------
lhs_gap = 1/(12*(z+a) - sp.Rational(1,4)) - U(z) + a**2/(2*z+a)
rhs_gap = (A*a**3 + B*a**2 + C*a + F) / (2520*z**5*(a+2*z)*(48*a+48*z-1))
diff = sp.simplify(sp.expand(lhs_gap - rhs_gap))
record("rational_gap_identity_symbolic", diff == 0, f"residual={diff}")

# shifted coefficients, own expansion
Bs = sp.expand(B.subs(z, t+1))
Cs_shift = None
expected_B = [120960, 723240, 1791720, 2353680, 1729056, 673512, 108600]  # t^6..t^0
got_B = [int(sp.expand(Bs).coeff(t, i)) for i in range(6, -1, -1)]
record("quadCoeff_shift_table", got_B == expected_B, f"got={got_B}")

D = 4*B*F - C**2  # discriminant complement (note: F is 'E' constant coeff)
Ds = sp.expand(D.subs(z, t+1))
expected_D = [203212800, 2149822080, 10299502080, 29404384380, 55375719840,
              71883106764, 65187512040, 40869159443, 17049349100, 4345739674,
              553547260, 16630775]  # t^11..t^0
got_D = [int(Ds.coeff(t, i)) for i in range(11, -1, -1)]
record("discriminant_shift_table", got_D == expected_D, f"got={got_D}")

# discriminant_identity: discriminant(z) == 4*B*F - C^2 exactly (as declared in Lean)
disc_lean = (203212800*z**11 - 85518720*z**10 - 22014720*z**9 - 79252740*z**8
             + 4294080*z**7 - 4020996*z**6 - 125664*z**5 + 63623*z**4 + 2688*z**3
             - 9188*z**2 - 384*z - 4)
record("discriminant_identity_symbolic", sp.expand(4*B*F - C**2 - disc_lean) == 0)

# quadratic positivity argument: 4B(Ba^2+Ca+F) = (2Ba+C)^2 + (4BF-C^2)
record("quadratic_completion_identity",
       sp.expand(4*B*(B*a**2 + C*a + F) - ((2*B*a + C)**2 + (4*B*F - C**2))) == 0)

# ---------- 4. upper step identity ----------
P = 112*z**8 + 448*z**7 + 1295*z**6 + 2317*z**5 + 2200*z**4 + 1061*z**3 + 253*z**2 + 34*z + 2
v = 1/(2*z+1)
H = (2*z+1)*(v + v**3/3 + v**5/5 + v**7/7 + v**9/(1-v**2)) - 1  # stepUpper-1 = (2z+1)*(...) -1
lhs_step = U(z) - U(z+1) - H
rhs_step = P / (2520*z**5*(z+1)**5*(2*z+1)**6)
diff2 = sp.simplify(sp.expand(lhs_step - rhs_step))
record("upper_step_identity_symbolic", diff2 == 0, f"residual={diff2}")
# P positive coefficients as declared
expected_P = [112, 448, 1295, 2317, 2200, 1061, 253, 34, 2]
got_P = [int(sp.Poly(P, z).coeff_monomial(z**i)) for i in range(8, -1, -1)]
record("stepNumerator_table", got_P == expected_P, f"got={got_P}")

# ---------- 1. literal identity mhat = R - E (numeric, 60 dps) ----------
def mhat(xv, av):
    xv = mp.mpf(xv); av = mp.mpf(av)
    # cancellation-free: work in logs
    y = xv + av
    logS = mp.log(2*mp.pi)/2 - mp.mpf(1)/2 + (y + mp.mpf(1)/2)*mp.log(y + mp.mpf(1)/2) - y
    return mp.loggamma(xv+1) + av*mp.log(xv+1) - logS

def R(zv):
    zv = mp.mpf(zv)
    return mp.loggamma(zv) - (zv - mp.mpf(1)/2)*mp.log(zv) + zv - mp.log(2*mp.pi)/2

def E(zv, av):
    zv = mp.mpf(zv); av = mp.mpf(av)
    return (zv + av)*mp.log(1 + av/zv) - av

# symbolic identity with positive symbols: mhat = R(z) - E(z,a)
zp, ap = sp.symbols('zp ap', positive=True)
mhat_sym = sp.loggamma(zp) + (ap + sp.Rational(1,2))*sp.log(zp) - sp.log(2*sp.pi)/2 \
           - ((zp+ap)*sp.log(zp+ap) - (zp+ap))
RE_sym = sp.loggamma(zp) - (zp - sp.Rational(1,2))*sp.log(zp) + zp - sp.log(2*sp.pi)/2 \
         - ((zp+ap)*sp.log(1+ap/zp) - ap)
d = sp.simplify(sp.expand_log(mhat_sym - RE_sym, force=True))
record("mhat_equals_R_minus_E_symbolic", sp.simplify(d) == 0, f"residual={d}")
worst = 0
for xv in [0, 0.3, 1.7, 10.5, 123.4]:
    for av in [0, 0.5, 1]:
        d = abs(mhat(xv, av) - (R(xv+1) - E(xv+1, av - 0.5)))
        worst = max(worst, d)
record("mhat_equals_R_minus_E_numeric", worst < mp.mpf('1e-15'),
       f"worst dev={mp.nstr(worst,3)} (mp.loggamma ulp level)")

# ---------- 2. constant k ----------
k = 12*(mp.e**(mp.mpf(1)/48) - 1)
record("k_in_quarter_half", mp.mpf(1)/4 <= k < mp.mpf(1)/2, f"k={mp.nstr(k,20)}")
# rewrite check: 12(x+alpha)+18-12e^{1/48} == 12(z+a)-k
lhs_c = 12*(x+alpha) + 18 - 12*sp.exp(sp.Rational(1,48))
rhs_c = 12*((x+1)+(alpha-sp.Rational(1,2))) - 12*(sp.exp(sp.Rational(1,48))-1)
record("bound_denominator_rewrite", sp.simplify(lhs_c - rhs_c) == 0)

# ---------- 5/6/7 numeric full-bound sweep ----------
def bound(yv):  # source bound b*_SC(y), y=x+alpha
    return 1/(12*yv + 18 - 12*mp.e**(mp.mpf(1)/48))

fails = []
min_margin = mp.inf
xs = [mp.mpf(i)/8 for i in range(0, 81)]           # x in [0,10] step 1/8
for xv in xs:
    for av in [mp.mpf(i)/8 for i in range(0, 9)]:  # alpha in [0,1] step 1/8
        m = mhat(xv, av); b = bound(xv+av)
        margin = b - m
        min_margin = min(min_margin, margin)
        if margin <= 0:
            fails.append((str(xv), str(av), mp.nstr(margin, 5)))
record("conjecture_strict_grid_693pts", not fails,
       f"min margin={mp.nstr(min_margin,6)}; fails={fails[:3]}")

# random high-precision sweep, incl alpha beyond 1 (claimed stronger a>=0)
import random
random.seed(20261027)
fails2 = []
min_margin2 = mp.inf
for _ in range(3000):
    xv = mp.mpf(random.random()) * mp.mpf(10)**mp.mpf(random.uniform(-2, 4))
    av = mp.mpf(random.random()) * mp.mpf(random.uniform(0, 3))
    if xv + av <= -0.5:  # not needed since xv>=0
        continue
    m = mhat(xv, av); b = bound(xv+av)
    min_margin2 = min(min_margin2, b - m)
    if b - m <= 0:
        fails2.append((mp.nstr(xv, 5), mp.nstr(av, 5)))
record("conjecture_strict_random_3000", not fails2, f"min margin={mp.nstr(min_margin2,6)}")

# boundary cases explicitly
bnd = {}
for xv, av, label in [(0,0,'x=0,a=0'), (0,mp.mpf(1)/2,'x=0,a=1/2'), (0,1,'x=0,a=1'),
                      (1,0,'x=1,a=0'), (1,mp.mpf(1)/2,'x=1,a=1/2'), (1,1,'x=1,a=1'),
                      (mp.mpf('0.001'), mp.mpf('0.999'), 'near corner')]:
    margin = bound(xv+av) - mhat(xv, av)
    bnd[label] = mp.nstr(margin, 8)
    if margin <= 0: record(f"boundary_{label}", False, mp.nstr(margin,5))
record("boundary_cases_positive_margin", True, json.dumps(bnd))

# U vs R classical check + U<=1/(12z)
worst_ur = -mp.inf
for i in range(1, 400):
    zv = mp.mpf(i)/4 + mp.mpf('0.01')
    worst_ur = max(worst_ur, R(zv) - U(zv))
record("R_le_U_numeric", worst_ur <= 0, f"max R-U = {mp.nstr(worst_ur,5)}")
worst_u = max(U(mp.mpf(i)/10 + 1) - 1/(12*(mp.mpf(i)/10 + 1)) for i in range(0, 200))
record("U_le_1_over_12z_numeric", worst_u <= 1e-55, f"max diff={mp.nstr(worst_u,3)}")

# entropy bounds
w1 = w2 = -mp.inf
for _ in range(500):
    zv = mp.mpf(random.random())*50 + mp.mpf('0.05')
    av = mp.mpf(random.random())*10
    Ev = (zv+av)*mp.log(1+av/zv) - av
    w1 = max(w1, -Ev)
    w2 = max(w2, av**2/(2*zv+av) - Ev)
record("entropy_nonneg_numeric", w1 <= 0, f"max -E={mp.nstr(w1,3)}")
record("entropy_lower_numeric", w2 <= 1e-50, f"max (a^2/(2z+a)-E)={mp.nstr(w2,3)}")

# ---------- 8. interpolation sandwich ----------
w3 = 0
for n in range(2, 30):
    for _ in range(20):
        r = mp.mpf(random.random())
        val = R(n+r)
        w3 = max(w3, (R(n) - 2/(n-1)) - val, val - (R(n) + 1/n))
record("unit_interval_sandwich_numeric", w3 <= 1e-45, f"worst violation={mp.nstr(w3,3)}")

n_fail = sum(1 for v in results.values() if not v["pass"])
print(f"\nTOTAL: {len(results)} checks, {n_fail} failures")
json.dump(results, open(__file__.replace('.py', '_results.json'), 'w'), indent=1)
sys.exit(1 if n_fail else 0)
