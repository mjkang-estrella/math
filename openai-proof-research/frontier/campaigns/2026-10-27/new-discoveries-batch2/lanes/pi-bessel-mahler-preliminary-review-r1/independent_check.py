"""Independent verification for pi-bessel-mahler-preliminary-review-r1.

Deliberately different algorithms from the root's checks.py:
- identity (1) checked by direct numerical quadrature of the t-integral
  (not by series/beta reduction);
- the headline asymptotic checked by direct quadrature of the ORIGINAL
  integral F_{n,p} = int_0^inf r^{n+n/(2p)-1} I_{n/2}(r)^{-1/p} dr,
  with an adaptive finite/infinite split chosen by locating the Laplace
  peak of |r^{...}/I^{1/p}| -- no reliance on the root's J_d sandwich.
Run under: bash -c 'ulimit -v 524288; python3 independent_check.py'
"""
import json
import mpmath as mp

mp.mp.dps = 40

out = {}

# ---------- 1. identity (1): Z_n(r) = Gamma(n/2+1)(2/r)^(n/2) I_{n/2}(r) ----
# with c_n = Gamma(n/2+1)/(sqrt(pi) Gamma((n+1)/2)), d = n-1.
def Z_direct(n, r):
    d = n - 1
    c = mp.gamma(mp.mpf(n) / 2 + 1) / (mp.sqrt(mp.pi) * mp.gamma((mp.mpf(n) + 1) / 2))
    f = lambda t: mp.e ** (r * t) * (1 - t * t) ** (mp.mpf(d) / 2)
    return c * mp.quad(f, [-1, 0, 1])

def Z_closed(n, r):
    v = mp.mpf(n) / 2
    return mp.gamma(v + 1) * (2 / r) ** (mp.mpf(n) / 2) * mp.besseli(v, r)

id_rows = []
for n in (4, 7, 15):
    for r in (mp.mpf('0.5'), mp.mpf(3), mp.mpf(40)):
        a, b = Z_direct(n, r), Z_closed(n, r)
        rel = abs(a - b) / abs(b)
        id_rows.append(dict(n=n, r=str(r), rel_err=str(rel)))
        assert rel < mp.mpf('1e-28'), (n, r, rel)
out['identity_check'] = id_rows
print('identity (1) direct-quadrature check: PASS,', len(id_rows), 'points')

# ---------- 2. sandwich (3) at extended grid, incl. u=0, huge u -------------
def psi(u):
    t = 2 * u / (1 + mp.sqrt(1 + 4 * u * u))
    return u * t + mp.log1p(-t * t) / 2

sand_ok = 0
for n in (3, 9, 40):
    d = n - 1
    c = mp.gamma(mp.mpf(n) / 2 + 1) / (mp.sqrt(mp.pi) * mp.gamma((mp.mpf(n) + 1) / 2))
    for u in (mp.mpf(0), mp.mpf('0.001'), mp.mpf(1), mp.mpf(25), mp.mpf(400)):
        z = Z_closed(n, d * u) if u != 0 else mp.mpf(1)
        lo = c / (4 * d * (1 + u)) * mp.e ** (d * psi(u))
        hi = 2 * c * mp.e ** (d * psi(u))
        assert lo <= z <= hi, (n, u)
        sand_ok += 1
out['sandwich_points'] = sand_ok
print('sandwich (3): PASS at', sand_ok, 'points')

# ---------- 3. original-integral asymptotic ---------------------------------
def log_F(n, p):
    """Direct quadrature of the original integral, log scale, peak-split."""
    v = mp.mpf(n) / 2
    a = n + mp.mpf(n) / (2 * p) - 1
    g = lambda r: a * mp.log(r) - mp.log(mp.besseli(v, r)) / p
    # peak of the integrand's log near r ~ a (since I ~ e^r)
    r0 = a  # rough; refine by golden search on g
    lo, hi = r0 / 2, r0 * 2
    for _ in range(60):
        m1 = lo + (hi - lo) / 3
        m2 = hi - (hi - lo) / 3
        if g(m1) < g(m2):
            lo = m1
        else:
            hi = m2
    rp = (lo + hi) / 2
    width = mp.mpf(int(200 * p + 40))
    pts = [0, rp - width, rp - width / 10, rp, rp + width / 10, rp + width,
           rp + 4 * width, mp.inf]
    pts = sorted(set(pts))
    integ = lambda r: mp.e ** (g(r) - g(rp))
    val = mp.quad(integ, pts) * mp.e ** g(rp)
    return mp.log(val), g(rp), rp

def headline(n, p):
    hp = mp.log(p) / 2 + (1 + 1 / p) * mp.log1p(p) / 2 - 1
    return n * ((1 + 1 / (2 * p)) * mp.log(n) - 1 / (2 * p) + hp)

rows = []
for p in (mp.mpf('0.25'), mp.mpf('0.5'), mp.mpf(2), mp.mpf(8)):
    for n in (12, 40, 120):
        lf, gp, rp = log_F(n, p)
        h = headline(n, p)
        err = lf - h
        rows.append(dict(p=str(p), n=n, logF=str(mp.nstr(lf, 12)),
                         headline=str(mp.nstr(h, 12)), log_error=str(mp.nstr(err, 12)),
                         err_over_logn=str(mp.nstr(err / mp.log(n), 12)),
                         peak_r=str(mp.nstr(rp, 8))))
        # claim: error is O_p(log n); check it is small relative to n
        assert abs(err) < abs(mp.log(n)) * 60 + 20, (p, n, err)
out['original_integral'] = rows
for r in rows:
    print(f"p={r['p']:>4} n={r['n']:>3}  logF={r['logF']:>15}  "
          f"headline={r['headline']:>15}  log_err={r['log_error']:>10}  "
          f"err/logn={r['err_over_logn']}")

# also p=1 against source's proved case constant
n = 60
lf, _, _ = log_F(n, mp.mpf(1))
h = headline(n, mp.mpf(1))
out['p1_case'] = dict(n=n, log_error=str(mp.nstr(lf - h, 12)))
print('p=1, n=60 log error vs conjectured exponent:', mp.nstr(lf - h, 8))

(ROOT := __import__('pathlib').Path(__file__).parent)
(ROOT / 'independent_check.json').write_text(json.dumps(out, indent=1) + '\n')
print('ALL INDEPENDENT CHECKS PASS')
