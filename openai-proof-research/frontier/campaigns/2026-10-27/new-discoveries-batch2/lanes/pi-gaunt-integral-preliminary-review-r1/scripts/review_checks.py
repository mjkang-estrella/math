#!/usr/bin/env python3
"""Independent adversarial review checks. mpmath only, single process, low memory.
Run under: bash -c 'ulimit -v 524288; python3 review_checks.py'
"""
from mpmath import mp, mpf, besselk, quad, sqrt, exp, cosh, sinh, findroot, inf
import random, json, math

mp.dps = 30
out = {"failures": [], "counts": {}}

def delta_of(n, nu):
    mu = nu + n
    r = mu*mu - 2*nu - 1
    if abs(r) < mpf("1e-9")*abs(mu*mu): r = mpf(0)   # float-threshold noise clamp
    return mu, sqrt(r)

def tail(n, nu, mu, x):
    f = lambda t: t**(-nu) * besselk(mu, t)
    return quad(f, [x, inf])

def check_ineq(n, nu, x, tag):
    mu, d = delta_of(n, nu)
    lhs = tail(n, nu, mu, x)
    rhs = x**(-nu) * besselk(d, x)
    if not (lhs > rhs):
        out["failures"].append(("conjecture", tag, n, nu, float(d), x, float(lhs), float(rhs)))
    # derivative comparison (2.18): d/dx[x^-nu K_delta] > -x^-nu K_mu, i.e.
    # K_mu > K_{delta-1} + (nu+delta)K_delta/x  (pointwise, delta>0)
    if d != 0:
        rhs2 = besselk(d-1, x) + (nu+d)*besselk(d, x)/x
        if not (besselk(mu, x) > rhs2):
            out["failures"].append(("three_order", tag, n, nu, float(d), x))
    return mu, d

# 1. Boundary delta=0 cases (radicand exactly 0): nu = 1-n+sqrt(2(1-n))
for n, nu in [(0.5, 1.5), (-1.0, 4.0), (-3.5, 7.5), (-8.0, 1-(-8)+mp.sqrt(mpf(18))), (0.0, 1+mp.sqrt(2))]:
    n, nu = mpf(n), mpf(nu)
    for x in [mpf("0.05"), mpf("0.3"), mpf(1), mpf(4), mpf(40)]:
        mu, d = delta_of(n, nu)
        assert abs(d) < mpf("1e-20"), (n, nu, d)
        lhs = tail(n, nu, mu, x)
        rhs = x**(-nu) * besselk(0, x)   # delta=0
        if not (lhs > rhs):
            out["failures"].append(("delta0", n, nu, float(x)))
        # zero-order tangent comparison: K_mu > K_1 + nu*K_0/x
        if not (besselk(mu, x) > besselk(1, x) + nu*besselk(0, x)/x):
            out["failures"].append(("delta0_tangent", n, nu, float(x)))
out["counts"]["delta0_cases"] = 25

# 2. Randomized sweep incl. negative n, near-threshold nu, large delta
random.seed(20261028)
N = 0
for trial in range(120):
    n = random.uniform(-25, 0.95)
    thr = 1 - n + math.sqrt(2*(1-n))
    nu = thr + random.choice([0, 0, 1e-6, 1e-3, random.uniform(0, 30)])
    for x in [mpf("0.02"), mpf("0.7"), mpf(1), mpf(7), mpf(60)]:
        check_ineq(mpf(n), mpf(nu), x, "rand")
        N += 1
out["counts"]["sweep"] = N

# 3. Sharpness: |eta|>delta must fail for large x. Test eta=delta+1.
fails_sharp = 0
for trial in range(12):
    n = random.uniform(-8, 0.9)
    thr = 1 - n + math.sqrt(2*(1-n))
    nu = thr + random.uniform(0, 10)
    mu, d = delta_of(mpf(n), mpf(nu))
    eta = d + 1
    broken = False
    for x in [mpf(30), mpf(60), mpf(120), mpf(240)]:
        lhs = tail(n, mpf(nu), mu, x)
        rhs = x**(-mpf(nu)) * besselk(eta, x)
        if lhs < rhs:
            broken = True
            break
    if broken: fails_sharp += 1
    else: out["failures"].append(("sharpness_not_broken", n, nu, float(d)))
out["counts"]["sharpness_broken"] = fails_sharp

# 4/4b/4c. Robust float64 checks with uniform e^x scaling (kve = K*e^z).
# Normalized units: Tn = int_0^inf e^-s (x+s)^-nu kve(mu,x+s) ds * x^(nu+1/2)/sqrt(pi/2)  (= tail/S)
#                   Kn(order r) = kve(r,x) * x^0.5 / sqrt(pi/2)                          (= x^-nu K_r / S)
import numpy as np
from scipy.integrate import quad as squad
from scipy.special import kve
SQ = np.sqrt(np.pi/2)
def admissible(nn, vv):
    thr = 1 - nn + math.sqrt(2*(1-nn))
    return thr + 0.4 if vv < thr else vv
coeff_errs = []; sharp = []; mainlx = []
for (nn, vv) in [(0.3, 3.4), (-2.0, 5.4), (0.8, 1.8), (-5.0, 8.0)]:
    vv = admissible(nn, vv)
    mm = vv + nn
    dd = math.sqrt(mm*mm - 2*vv - 1); et = dd + 1
    for x in [60., 150., 300.]:
        Tn = squad(lambda s: np.exp(-s)*kve(mm, x+s)/(x+s)**vv, 0, np.inf,
                   epsabs=0, epsrel=1e-13, limit=1000)[0]*x**(vv+0.5)/SQ
        pred = (dd*dd - et*et)/2/x
        got = Tn - kve(et, x)*x**0.5/SQ
        rel = abs(got-pred)/abs(pred)
        coeff_errs.append(rel)
        if rel > 0.05:
            out["failures"].append(("asymptotic_coefficient", nn, vv, x, rel))
        if x == 300.:
            sharp.append((nn, vv, got))
            if got >= 0: out["failures"].append(("sharpness_scaled", nn, vv, got))
            mainlx.append((nn, vv, Tn - kve(dd, x)*x**0.5/SQ))
            if mainlx[-1][2] <= 0: out["failures"].append(("large_x_ineq", nn, vv, mainlx[-1][2]))
out["counts"]["asymptotic_max_rel_err"] = max(coeff_errs)
out["counts"]["sharpness_scaled_negative"] = f"{sum(1 for g in sharp if g[2]<0)}/{len(sharp)}"
out["counts"]["large_x_ineq_positive"] = f"{sum(1 for g in mainlx if g[2]>0)}/{len(mainlx)}"
print(json.dumps(out, indent=1))
