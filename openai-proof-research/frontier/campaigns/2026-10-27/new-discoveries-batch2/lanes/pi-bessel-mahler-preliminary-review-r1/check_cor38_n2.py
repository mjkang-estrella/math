"""Verify Corollary 3.8's prefactor exactly at n=2 (unit disk), and check which
M_p(B_2^2) constant follows from F_{2,p}: the Conjecture 5.1 constant
(2*pi*sqrt((1+p)^((1+p)/p)/p))^n or pi*2^((1+1/p)/2)*sqrt(...).

n=2: h_{B,p}(r) = (1/p) log[ (1/pi) * 2*pi*I_1(p r)/(p r) ]
     M_p(B) = pi * 2*pi * int_0^inf e^{-h(r)^p} r dr
Cor 3.8 at n=2: M_p(B_2^2) = 2*pi^2/(2^1 * p^2 * Gamma(2)^{2+1/p}) * F_{2,p}
              = pi^2/p^2 * F_{2,p},
F_{2,p} = int_0^inf r^{1+1/p} I_1(r)^{-1/p} dr.
"""
import mpmath as mp

mp.mp.dps = 40

def M_geom(p):
    h = lambda r: mp.log(2 * mp.besseli(1, p * r) / (p * r)) / p if r else mp.mpf(0)
    f = lambda r: mp.e ** (-h(r) ** p) * r if r else mp.mpf(0)
    return 2 * mp.pi ** 2 * mp.quad(f, [0, 1, 5, 20, 100, mp.inf])

def F_num(p):
    # r^{1+1/p} I_1(r)^{-1/p}: log-integrand peak find in x=log r
    a = 1 + 1 / p
    g = lambda x: a * x - mp.log(mp.besseli(1, mp.e ** x)) / p + x
    xs = [mp.mpf(i) / 4 for i in range(-40, 200)]
    best = max(xs, key=g)
    lo, hi = best - 1, best + 1
    for _ in range(60):
        m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        lo, hi = (lo, m2) if g(m1) < g(m2) else (m1, hi)
    xp = (lo + hi) / 2
    W = 60 * p + 30
    f = lambda x: mp.e ** (g(x) - g(xp))
    val = mp.quad(f, [xp - W, xp - 8, xp - 2, xp, xp + 2, xp + 8, xp + W])
    return mp.e ** g(xp) * mp.re(val)

def F_sandwich_exact(p):
    """F via the exact u-integral route (identity (1)), n=2."""
    d = 1
    up = mp.sqrt(p * (1 + p))
    G = lambda w: d * w - (mp.loggamma(2) + mp.log(2 / (mp.e ** w))) / p + w \
        - mp.log(mp.besseli(1, d * mp.e ** w)) / p
    w0 = mp.log(up)
    xs = [w0 + mp.mpf(i) / 4 - 10 for i in range(81)]
    best = max(xs, key=G)
    lo, hi = best - 1, best + 1
    for _ in range(60):
        m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        lo, hi = (lo, m2) if G(m1) < G(m2) else (m1, hi)
    wp = (lo + hi) / 2
    W = 20 + 40 / mp.sqrt(d * (1 + 1 / p))
    f = lambda w: mp.e ** (G(w) - G(wp))
    val = mp.quad(f, [wp - W, wp - 4, wp - 1, wp, wp + 1, wp + 4, wp + W])
    # F = [Gamma(2)2^{1}]^{1/p} d^2 * int u^{d} Z(du)^{-1/p} du, d=1:
    # u-integral = int_0^inf u Z_2(u)^{-1/p} du with Z_2(u)=Gamma(2)(2/u)^1 I_1(u)
    # G(w) already = log[ u^1 * Z_2(e^w)^{-1/p} * u ] (du = u dw)
    return 2 ** (1 / p) * 1 ** 2 * mp.e ** G(wp) * mp.re(val)

for p in (mp.mpf('0.5'), mp.mpf(1), mp.mpf(2)):
    mg = M_geom(p)
    f1 = F_num(p)
    f2 = F_sandwich_exact(p)
    cor38 = mp.pi ** 2 / p ** 2 * f1
    print(f"p={p}: M_geom={mp.nstr(mg, 10)}  F_num={mp.nstr(f1, 10)}  "
          f"F_exact_route={mp.nstr(f2, 10)}  diffF={mp.nstr(f1 - f2, 6)}")
    print(f"   Cor3.8(M)= {mp.nstr(cor38, 10)}  vs geometric {mp.nstr(mg, 10)}"
          f"  ratio {mp.nstr(cor38 / mg, 8)}")
    # candidate constants (n=2): (const)^2
    c51 = 2 * mp.pi * mp.sqrt((1 + p) ** ((1 + p) / p) / p)
    cmine = mp.pi * 2 ** ((1 + 1 / p) / 2) * mp.sqrt((1 + p) ** (1 + 1 / p) / p)
    print(f"   sqrtM/const: 5.1const {mp.nstr((mg / (c51 ** 2)) ** 0.5, 8)}"
          f"  myconst {mp.nstr((mg / (cmine ** 2)) ** 0.5, 8)}")
