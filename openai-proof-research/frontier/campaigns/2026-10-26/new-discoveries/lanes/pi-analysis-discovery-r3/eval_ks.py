"""Robust high-precision evaluation of E_{alpha,m,l}(-x) and checks of MathDB 348998
(Boudabsa-Simon 2012.05666, Conjecture 4.5).

Series: u(x) = sum_n a_n (-x)^n, a_n = prod_{j=0}^{n-1} G(j), 
G(j) = Gamma(1+alpha(j m + l))/Gamma(1+alpha(j m + l + 1)).

Alternating sum with huge cancellation -> adaptive dps from peak-term magnitude.
"""
from mpmath import mp, mpf, gamma, power, exp, loggamma
from math import lgamma
import math

def r_log(s, a):
    "log r(s), r(s)=Gamma(1+a s)/Gamma(1+a(s+1))"
    return lgamma(1 + a*s) - lgamma(1 + a*(s+1))

def find_nstar(a, m, l, x):
    "min n with x*r((n-1)m+l) <= 1 (ratio of term n to term n-1). r decreasing in n."
    if x <= 1: return 5
    lo, hi = 1, 2
    while x*math.exp((lgamma(1+a*(hi*m+l)) - lgamma(1+a*(hi*m+l+1)))) > 1:
        hi *= 2
        if hi > 10**8: raise RuntimeError("nstar too big")
    while hi - lo > 1:
        mid = (lo+hi)//2
        rr = x*math.exp(lgamma(1+a*((mid-1)*m+l)) - lgamma(1+a*((mid-1)*m+l+1)))
        if rr > 1: lo = mid
        else: hi = mid
    return hi

def log_peak(a, m, l, x, nstar):
    "log|a_{n*} x^{n*}| via incremental lgamma sums (float)"
    s = nstar * math.log(x) if x >= 1 else nstar*math.log(max(x,1e-300))
    acc = 0.0
    for j in range(nstar):
        acc += lgamma(1+a*(j*m+l)) - lgamma(1+a*(j*m+l+1))
    return s + acc

def eval_u(a, m, l, x, extra_dps=80):
    x = mpf(x)
    nstar = find_nstar(a, m, l, float(x))
    lp = log_peak(a, m, l, float(x), nstar)
    dps = int(max(50, lp/math.log(10))) + extra_dps
    old = mp.dps; mp.dps = dps
    try:
        N = nstar + 3000
        # coefficients (mp precision!)
        a_coefs = [mpf(1)]
        cur = mpf(1)
        for n in range(1, N+1):
            cur = cur * exp(loggamma(1+a*((n-1)*m+l)) - loggamma(1+a*((n-1)*m+l+1)))
            a_coefs.append(cur)
        u = mpf(0); d1 = mpf(0)
        for n in range(N+1):
            t = a_coefs[n] * power(-x, n)
            u += t
            if n >= 1:
                d1 -= n * a_coefs[n] * power(-x, n-1)
        return u, d1, dict(nstar=nstar, dps=dps, N=N)
    finally:
        mp.dps = old

# ---------------- checks ----------------
def r(s, a):
    return gamma(1 + a*s) / gamma(1 + a*(s+1))

def check_point(a, m, l, x):
    u, d1, info = eval_u(a, m, l, x)
    c1 = r(l - m, a); c2 = r(l, a)
    lo = 1/(1 + c1*x); hi = 1/(1 + c2*x)
    res = dict(
        u=u, lo=lo, hi=hi,
        e_lo=u - lo,          # want >= 0
        e_hi=hi - u,          # want >= 0
        di=c1*u*u + d1,       # want >= 0   (-u' <= c1 u^2)
        di2=c2*u*u + d1,      # want <= 0? (upper bound differential form) check
        phi=(1/u - 1)/x,
        info=info)
    return res

def sweep(alphas, ms, ls, xs):
    bad = []
    for a in alphas:
        for m in ms:
            for l in ls:
                if not (l > m - 1/a): continue
                prev_phi = None
                mono_min = None
                for x in xs:
                    res = check_point(a, m, l, x)
                    for k in ['e_lo', 'e_hi', 'di']:
                        if res[k] < -mpf(10)**(-30):
                            bad.append((float(a), float(m), float(l), float(x), k, float(res[k])))
                    if prev_phi is not None:
                        dphi = res['phi'] - prev_phi
                        if mono_min is None or dphi < mono_min: mono_min = dphi
                        if dphi < -mpf(10)**(-25):
                            bad.append((float(a), float(m), float(l), float(x), 'mono', float(dphi)))
                    prev_phi = res['phi']
                tag = "FAIL" if any(b[0:4]==(float(a),float(m),float(l),b[3]) for b in bad) else "ok"
                print(f"a={float(a):.4g} m={float(m):.4g} l={float(l):.4g} {tag} mono_min={mono_min if mono_min is None else float(mono_min):.3g}", flush=True)
    return bad

if __name__ == "__main__":
    import sys
    mode = sys.argv[1] if len(sys.argv) > 1 else "test"
    if mode == "test":
        # cross-check alpha=1: u = _1F_1(1;(l+1)/m;-x/m)
        from mpmath import hyp1f1, erfc
        for (a, m, l, x) in [(1, 2, mpf(3)/2, 5), (1, mpf(3), mpf(7)/3, 2), (mpf(1)/2, 1, 2, 10)]:
            u, d1, info = eval_u(a, m, l, x)
            if a == 1:
                ref = hyp1f1(1, (l+1)/m, -x/m)
            else:
                ref = None
            print((a,m,l,float(x)), "u=", mp.nstr(u, 20), "ref=", mp.nstr(ref,20) if ref else "-", info)
        # known: E_{1/2,1,1/2}(-x) = E_{1/2}(-x) = e^{x^2} erfc(x)
        u, d1, info = eval_u(mpf(1)/2, 1, mpf(1)/2, mpf(3))
        ref = exp(mpf(9)) * erfc(3)
        print("E_{1/2,1,1/2}(-3) =", mp.nstr(u, 25), " e^9 erfc(3) =", mp.nstr(ref, 25))
    elif mode == "point":
        a, m, l, x = mpf(sys.argv[2]), mpf(sys.argv[3]), mpf(sys.argv[4]), mpf(sys.argv[5])
        res = check_point(a, m, l, x)
        for k in ['u','lo','hi','e_lo','e_hi','di','phi']:
            print(k, mp.nstr(res[k], 25))
        print(res['info'])
    elif mode == "sweep":
        xs = [mpf(10)**(k/8) for k in range(-24, 9)] + [mpf(k) for k in range(9, 61)]
        bad = sweep([mpf(p)/100 for p in [10, 25, 50, 75, 90, 99]], [mpf(1)/10, mpf(1)/2, 1, 2, 5], 
                    [], xs) if False else None
        bad = []
        for a in [mpf(p)/100 for p in [10, 25, 50, 75, 90, 99]]:
            for m in [mpf(1)/10, mpf(1)/2, 1, 2, 5]:
                base = m - 1/a
                for loff in [mpf(1)/20, mpf(1)/2, 1, 3, 10]:
                    l = base + loff
                    bad += sweep([a], [m], [l], xs)
        print("VIOLATIONS:", len(bad))
        for b in bad[:20]: print(b)
