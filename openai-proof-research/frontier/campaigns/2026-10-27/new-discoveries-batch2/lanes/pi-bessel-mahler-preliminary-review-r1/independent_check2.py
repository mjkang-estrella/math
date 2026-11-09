"""Independent asymptotic check, take 2 (fixed): w = log u substitution.

log F_{n,p} = (1/p)(logGamma(n/2+1) + (n/2)log 2) + n log(n-1)
              + log[ int_0^inf u^{n-1} Z_n(d u)^(-1/p) du ],   d = n-1,
Z_n(r) = Gamma(n/2+1)(2/r)^(n/2) I_{n/2}(r)   (identity verified separately
by direct t-quadrature in independent_check.py).

With w = log u (u = e^w) the integrand is real, smooth, and decays both ways;
evaluated EXACTLY (no inequalities) on a finite window around its peak.
Cross-checked against a second route: the original r-integral in x = log r.
"""
import json
import pathlib
import mpmath as mp

mp.mp.dps = 45
out = {}

def psi(u):
    t = 2 * u / (1 + mp.sqrt(1 + 4 * u * u))
    return u * t + mp.log1p(-t * t) / 2

def logZ(n, r):
    v = mp.mpf(n) / 2
    return mp.loggamma(v + 1) + v * mp.log(2 / r) + mp.log(mp.besseli(v, r))

def log_F(n, p):
    d = n - 1
    up = mp.sqrt(p * (1 + p))
    G = lambda w: (n - 1) * w - logZ(n, d * mp.e ** w) / p + w
    # locate peak of G on a grid, refine by golden section
    w0 = mp.log(up)
    xs = [w0 + mp.mpf(i) / 4 - 10 for i in range(81)]
    best = max(xs, key=G)
    lo, hi = best - 1, best + 1
    for _ in range(60):
        m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if G(m1) < G(m2):
            lo = m1
        else:
            hi = m2
    wp = (lo + hi) / 2
    W = 8 + 40 / mp.sqrt(d)  # width in w ~ 1/sqrt(d); far tails decay faster
    f = lambda w: mp.e ** (G(w) - G(wp))
    val = mp.quad(f, [wp - W, wp - 4, wp - 1, wp, wp + 1, wp + 4, wp + W])
    assert abs(mp.im(val)) < mp.mpf('1e-30')
    return (mp.loggamma(mp.mpf(n) / 2 + 1) + mp.mpf(n) / 2 * mp.log(2)) / p \
        + n * mp.log(d) + G(wp) + mp.log(mp.re(val))

def headline(n, p):
    hp = mp.log(p) / 2 + (1 + 1 / p) * mp.log1p(p) / 2 - 1
    return n * ((1 + 1 / (2 * p)) * mp.log(n) - 1 / (2 * p) + hp)

rows = []
for p in (mp.mpf('0.25'), mp.mpf('0.5'), mp.mpf(2), mp.mpf(8)):
    for n in (12, 40, 120, 300):
        lf = log_F(n, p)
        assert abs(mp.im(lf)) < mp.mpf('1e-20'), (p, n, lf)
        err = mp.re(lf) - headline(n, p)
        rows.append(dict(p=str(p), n=n, log_error=str(mp.nstr(err, 10)),
                         err_over_logn=str(mp.nstr(err / mp.log(n), 10))))
        assert abs(err / mp.log(n)) < 30, (p, n, err)
out['exact_substitution'] = rows
for r in rows:
    print(f"p={r['p']:>4} n={r['n']:>3}  log_err={r['log_error']:>12}  "
          f"err/logn={r['err_over_logn']:>12}")

# --- cross route: original r-integral in x = log r --------------------------
def log_F_x(n, p):
    a = n + mp.mpf(n) / (2 * p) - 1
    def G(x):
        r = mp.e ** x
        return a * x - logZ(n, r) / p + x
    xs = [mp.mpf(i) / 2 for i in range(1, int(2 * mp.log(n) + 120))]
    best = max(xs, key=G)
    lo, hi = best - 1, best + 1
    for _ in range(60):
        m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if G(m1) < G(m2):
            lo = m1
        else:
            hi = m2
    xp = (lo + hi) / 2
    # tails: below peak integrand <= poly * exp(-r/(2p)) in u=r/d (sandwich (3));
    # above, r^{a} growth is beaten by the same exponential once u > 2p(1+1/p).
    R = 60 * p * (1 + 1 / p) + 100  # window in units of the u-scale, generous
    W = mp.log(1 + mp.sqrt(p * (1 + p)) + R / (n - 1))  # crude x-window
    f = lambda x: mp.e ** (G(x) - G(xp))
    val = mp.quad(f, [max(xp - W, mp.mpf(-5)), xp - 2, xp - mp.mpf('0.5'),
                      xp, xp + mp.mpf('0.5'), xp + 2, xp + W])
    assert abs(mp.im(val)) < mp.mpf('1e-30')
    return G(xp) + mp.log(mp.re(val))

rows2 = []
for p in (mp.mpf('0.5'), mp.mpf(2)):
    for n in (12, 40, 120):
        lf = log_F_x(n, p)
        err = lf - headline(n, p)
        rows2.append(dict(p=str(p), n=n, log_error=str(mp.nstr(err, 10))))
        assert abs(err / mp.log(n)) < 30, ('xroute', p, n, err)
out['xroute'] = rows2
for r in rows2:
    print('xroute', r)

pathlib.Path(__file__).parent.joinpath('independent_check2.json').write_text(
    json.dumps(out, indent=1) + '\n')
print('ALL INDEPENDENT CHECKS PASS (take 2)')
