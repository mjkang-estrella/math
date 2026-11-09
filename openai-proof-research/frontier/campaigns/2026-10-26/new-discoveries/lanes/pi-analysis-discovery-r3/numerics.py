"""Numeric exploration of MathDB 348998 = Boudabsa-Simon 2012.05666 Conjecture 4.5. v2

E_{alpha,m,l}(-x) = sum_n a_n (-x)^n, a_n = prod_{k=0}^{n-1} r(km+l),
r(s) = Gamma(1+alpha s)/Gamma(1+alpha(s+1)).

Checks (x in moderate range with exact series; tail via residue expansion):
 (A) 1/(1+c1 x) <= u <= 1/(1+c2 x), c1=r(l-m), c2=r(l)
 (B) phi(x) = (1/u - 1)/x nondecreasing
 (C) (DI): c1*u^2 + u' >= 0
"""
from mpmath import mp, mpf, gamma, power

mp.dps = 40

def r(s, a):
    return gamma(1 + a*s) / gamma(1 + a*(s+1))

def coeffs(a, m, l, N):
    out = [mpf(1)]
    for n in range(1, N+1):
        out.append(out[-1] * r((n-1)*m + l, a))
    return out

def need_terms(a, m, l, x, safety=6):
    # peak term index n* ~ (x/(a m))^{1/a}; go 4x beyond
    if a == 1: return int(x/ m) + 200
    ns = int(safety * power(x/(a*m), 1/a)) + 300
    return min(ns, 400000)

def u_series(a, m, l, x, N=None):
    if N is None: N = need_terms(a, m, l, x)
    # peak term index n* ~ (x/(a m))^{1/a}; never break before 3*n*
    if a == 1: npk = x/m
    else: npk = float(power(x/(a*m), 1/a))
    c = coeffs(a, m, l, N)
    u = mpf(0); d1 = mpf(0)
    xs = mpf(x)
    for n in range(N+1):
        t = c[n] * power(-xs, n)
        u += t
        if n >= 1: d1 -= n * c[n] * power(-xs, n-1)
        if n > max(3*npk, 100) and abs(t) < mpf(10)**(-42):
            break
    return u, d1, N

def residue_As(a, m, l, K):
    "A_k for k=1..K in u(x) ~ sum A_k x^-k"
    d = 1/(a*m)
    ca = (a*l + 1)*d      # c
    cb = 1/m + ca         # b
    def Q(s):
        return power(( ( (a*l+1)*d ),), 0)  # placeholder
    def poch_m1(s):  # [c; d]_{-s} = G(c-s)/G(c)
        return gamma(ca - s) / gamma(ca) if False else None
    # [c;delta]_{-s} = G(c-s;delta)/G(c;delta); use functional eq G(z+1)=Gamma(z/delta)G(z)
    def Gm(z):  # G(z;delta)/G(1;delta) not needed; use ratio identity:
        return None
    # Direct: [c;delta]_{-s} = prod_{j=1}^{J} Gamma((c-s-j)/delta)^{-1}... use formula
    # G(c-s)/G(c) with c = ca: G(z;delta) satisfies G(z+1)=Gamma(z/delta)G(z).
    # => G(c-s)/G(c) = 1/prod_{j=0}^{J-1} Gamma((c-s-1-j)/delta) ... times G(c-s-J)/G(c-J)
    # Easier: [c;delta]_{-s} = 1/([c-s+... ]) use: [c;delta]_{-s} = [c-s; delta]_{s}^{-1}... no.
    # Use: [c;delta]_{-s} = Gamma((c-s)/delta - ?)...
    # Simplest: G(z;delta) = prod_{k>=1} k^{?}... use identity G(z;delta) = delta^{(z-1)(z-2)/2...} skip.
    # Implement G(z;delta) via recursion to fractional base:
    def G(z):
        # reduce z to (0,1] and collect gammas
        gam = mpf(1)
        while z > 1 + mpf('1e-30'):
            z -= 1
            gam *= gamma(z / d)
        return gam * G_base(z)
    # G_base on (0,1] unknown... but ratios only need G(c-s)/G(c) with same fractional part
    # when s integer: c-s has same frac part as c. So ratio = 1/prod Gamma((c-j-s)/d)/Gamma((c-j)/d)
    def ratio_c(s):  # G(c-s)/G(c)
        p = mpf(1)
        j = 0
        while ca - 1 - j - s > -1 + mpf('1e-30') or j < 3:
            # reduce until argument in (0,1]-ish; both sides same frac part
            p *= gamma((ca - 1 - j) / d) / gamma((ca - 1 - j - s) / d)
            j += 1
            if j > 100000: raise RuntimeError
        # remaining: G(c-1-j-s)/G(c-1-j) with both args in (0,1] -> =1 (same frac part)
        return 1/p
    def ratio_b(s):
        p = mpf(1)
        j = 0
        while cb - 1 - j - s > -1 + mpf('1e-30') or j < 3:
            p *= gamma((cb - 1 - j) / d) / gamma((cb - 1 - j - s) / d)
            j += 1
            if j > 100000: raise RuntimeError
        return 1/p
    A = []
    for k in range(1, K+1):
        # residue of Gamma(s)Gamma(1-s) at s=k is: Gamma(s)~1, Gamma(1-s) res = (-1)^{k-1}/(k-1)! *(-1)?
        # Gamma(1-s) near s=k: 1-s = -(k-1) - (s-k); Gamma(-n+eps) res (-1)^n/n!
        # => res = (-1)^{k-1}/(k-1)! * (-1)?? compute directly: let s=k+e: 1-s=-k+1-e
        # Gamma(-n+e) ~ (-1)^n/(n! e) with n=k-1: res at s=k is (-1)^{k-1}/(k-1)! times -1 (since e=k-s)
        # (s-k)Gamma(1-s) -> -(-1)^{k-1}/(k-1)! = (-1)^k/(k-1)!
        res_gamma = power(-1, k) / gamma(k)  # (s-k) Gamma(1-s) |_{s=k}
        Qk = ratio_c(k) / ratio_b(k)  # [(c);delta]_{-k} / [b;delta]_{-k} = (G(c-k)/G(c))/(G(b-k)/G(b))
        A.append(res_gamma * Qk)
    return A

def u_tail(a, m, l, x, K=12):
    A = residue_As(a, m, l, K)
    s = mpf(0)
    for k, Ak in enumerate(A, start=1):
        s += Ak / power(x, k)
    return s, A

def check(a, m, l, xs, verbose=False):
    c1 = r(l - m, a); c2 = r(l, a)
    worst = dict(lo=mpf(10)**9, hi=mpf(10)**9, di=mpf(10)**9, mono=mpf(10)**9)
    prev_phi = None
    for x in xs:
        u, d1, N = u_series(a, m, l, x)
        lo = 1/(1 + c1*x); hi = 1/(1 + c2*x)
        worst['lo'] = min(worst['lo'], u - lo)
        worst['hi'] = min(worst['hi'], hi - u)
        worst['di'] = min(worst['di'], c1*u*u + d1)
        phi = (1/u - 1)/x
        if prev_phi is not None:
            worst['mono'] = min(worst['mono'], phi - prev_phi)
        prev_phi = phi
        if verbose:
            print(f"  x={float(x):12.5g} u={float(u):.14g} lo={float(lo):.14g} hi={float(hi):.14g} phi={float(phi):.14g} N={N}")
    return worst

def check_tail(a, m, l, xs, K=14):
    c1 = r(l - m, a); c2 = r(l, a)
    worst = dict(lo=mpf(10)**9, hi=mpf(10)**9)
    for x in xs:
        u, A = u_tail(a, m, l, x, K)
        # rigorous-ish: error bounded by next-term scale *if* asymptotic alternating-ish; just report
        lo = 1/(1 + c1*x); hi = 1/(1 + c2*x)
        worst['lo'] = min(worst['lo'], u - lo)
        worst['hi'] = min(worst['hi'], hi - u)
    return worst

if __name__ == "__main__":
    import sys
    mode = sys.argv[1] if len(sys.argv) > 1 else "sweep"
    if mode == "sweep":
        fails = []
        for a in [mpf(1)/4, mpf(1)/2, mpf(3)/4, mpf(9)/10, mpf(99)/100]:
            for m in [mpf(1)/10, mpf(1)/2, mpf(1), mpf(2), mpf(5)]:
                lo_l = m - 1/a
                for l in [lo_l + mpf(1)/20, lo_l + mpf(1)/2, lo_l + 1, lo_l + 3, lo_l + 10]:
                    if l <= m - 1/a: continue
                    xmax = 20 if a >= mpf(1)/2 else 8
                    xs = [mpf(10)**(k/6) for k in range(-18, 0)] + [mpf(k)/4 for k in range(5, int(4*xmax)+1)]
                    res = check(a, m, l, xs)
                    bad = (res['lo'] < -mpf(10)**-25 or res['hi'] < -mpf(10)**-25
                           or res['di'] < -mpf(10)**-25 or res['mono'] < -mpf(10)**-25)
                    tag = "FAIL" if bad else "ok"
                    if bad: fails.append((a, m, l, dict((k, float(v)) for k, v in res.items())))
                    print(f"a={float(a):.3g} m={float(m):.3g} l={float(l):.4g} {tag} "
                          f"lo={float(res['lo']):.3g} hi={float(res['hi']):.3g} "
                          f"di={float(res['di']):.3g} mono={float(res['mono']):.3g}", flush=True)
        print("fails:", len(fails))
        for f in fails[:10]: print(f)
    elif mode == "one":
        a, m, l = mpf(sys.argv[2]), mpf(sys.argv[3]), mpf(sys.argv[4])
        xs = [mpf(10)**(k/8) for k in range(-18, 12)] + [mpf(k)/2 for k in range(25, 121)]
        res = check(a, m, l, xs, verbose=True)
        print(res)
        for xmax, K in [(200, 16), (2000, 16), (20000, 16)]:
            xs2 = [mpf(xmax)*mpf(k)/10 for k in range(1, 11)]
            print("tail", xmax, {k: float(v) for k, v in check_tail(a, m, l, xs2, K).items()})
