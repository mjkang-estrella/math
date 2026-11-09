"""Cross-validation: my exact w-substitution log F at the root's own (p,n)
grid points; values must match root checks.json asymptotic_diagnostics."""
import mpmath as mp

mp.mp.dps = 45

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
    W = 8 + 40 / mp.sqrt(d)
    f = lambda w: mp.e ** (G(w) - G(wp))
    val = mp.quad(f, [wp - W, wp - 4, wp - 1, wp, wp + 1, wp + 4, wp + W])
    return (mp.loggamma(mp.mpf(n) / 2 + 1) + mp.mpf(n) / 2 * mp.log(2)) / p \
        + n * mp.log(d) + G(wp) + mp.log(mp.re(val))

def headline(n, p):
    hp = mp.log(p) / 2 + (1 + 1 / p) * mp.log1p(p) / 2 - 1
    return n * ((1 + 1 / (2 * p)) * mp.log(n) - 1 / (2 * p) + hp)

# root checks.json log_error values:
root = {('0.5', 10): 3.704456846039, ('0.5', 30): 4.253946877834,
        ('0.5', 80): 4.744775244314, ('1.0', 10): 1.892697299262,
        ('1.0', 30): 1.895278310444, ('1.0', 80): 1.896196953218,
        ('2.0', 10): 0.939523974058, ('2.0', 30): 0.665618320361,
        ('2.0', 80): 0.420660923495, ('5.0', 10): 0.312069919453,
        ('5.0', 30): -0.12963879894, ('5.0', 80): -0.52268492790}
for (ps, n), rv in root.items():
    p = mp.mpf(ps)
    mine = log_F(n, p) - headline(n, p)
    print(f"p={ps} n={n}: mine={mp.nstr(mine, 10)}  root={rv}  "
          f"diff={mp.nstr(mine - rv, 6)}")
    assert abs(mine - rv) < mp.mpf('1e-6'), (ps, n)
print('CROSS-VALIDATION vs root checks.json: ALL MATCH')
