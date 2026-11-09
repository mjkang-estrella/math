"""Independent final-review numerics for Gaunt339406 classification.
mpmath only, single process. Diagnostics only, not proof.
"""
import mpmath as mp
mp.mp.dps = 30

def tail(nu, order, x):
    # int_x^inf t^-nu K_order(t) dt; K via mpmath besselk
    f = lambda t: t ** (-nu) * mp.besselk(order, t)
    # split: [x, x+10] quad + tail via scaled substitution to control decay
    return mp.quad(f, [x, mp.inf])

def check_literal(n, nu, r, xs):
    d = mp.sqrt(max(mp.mpf(0), (nu + n) ** 2 - 2 * nu - 1))
    out = []
    for x in xs:
        lhs = x ** (-nu) * mp.besselk(r, x)
        rhs = tail(nu, nu + n, x)
        out.append((x, lhs < rhs, rhs - lhs))
    return d, out

fails = 0
cases = 0
xs = [mp.mpf("0.05"), mp.mpf("0.7"), mp.mpf(1), mp.mpf(4), mp.mpf(20)]
mp.mp.dps = 25
rng = [(n, nu) for n in [-20, -5, -1, mp.mpf("-0.5"), 0, mp.mpf("0.9")]
       for nu in [1 - n + mp.sqrt(2 * (1 - n)),
                  1 - n + mp.sqrt(2 * (1 - n)) + 3,
                  1 - n + mp.sqrt(2 * (1 - n)) + 40]]
print("== lower bound at r=delta and |r|<delta; failure at r=delta+1 (large x) ==")
for (n, nu) in rng:
    d = mp.sqrt(max(mp.mpf(0), (nu + n) ** 2 - 2 * nu - 1))
    # r = delta, r = 0.5*delta (or 0), negative -delta
    for r in [d, d / 2 if d > 0 else mp.mpf(0), -d]:
        for x in xs:
            cases += 1
            lhs = x ** (-nu) * mp.besselk(r, x)
            rhs = tail(nu, nu + n, x)
            if not (lhs < rhs):
                fails += 1
                print("FAIL", n, nu, r, x, lhs, rhs)
print("lower-bound cases:", cases, "failures:", fails)

# eventual failure: r = delta + s > delta. Use comparisonBessel D(x) = K_mu - K_{r-1} - (nu+r)K_r/x
# its eventual negativity is equivalent (via proved FTC) to tail failure; check D<0 AND
# directly verify tail failure by quadrature at a moderate x for a few cases.
fails2 = 0; cases2 = 0
print("== optimality: D(x) = K_mu - K_{r-1} - (nu+r)K_r/x eventually negative, r>d ==")
for (n, nu) in rng:
    d = mp.sqrt(max(mp.mpf(0), (nu + n) ** 2 - 2 * nu - 1))
    for s in [mp.mpf("0.3"), mp.mpf(1), mp.mpf(7)]:
        r = d + s
        neg_at = None
        for x in [2, 5, 10, 30, 100, 300, 1000]:
            D = mp.besselk(nu + n, x) - mp.besselk(r - 1, x) - (nu + r) / x * mp.besselk(r, x)
            if D < 0:
                neg_at = x
                break
        cases2 += 1
        if neg_at is None:
            fails2 += 1
            print("FAIL eventual-neg", n, nu, r)
print("optimality cases:", cases2, "failures:", fails2)

# direct tail-failure quadrature check at moderate x (x=5,10)
fails3 = 0; cases3 = 0
print("== direct tail check: int_x^inf t^-nu K_mu < x^-nu K_r for r>d ==")
for (n, nu) in rng[:6]:
    d = mp.sqrt(max(mp.mpf(0), (nu + n) ** 2 - 2 * nu - 1))
    for r in [d + mp.mpf("0.5"), d + 2]:
        for x in [mp.mpf(5), mp.mpf(12), mp.mpf(40)]:
            lhs = x ** (-nu) * mp.besselk(r, x)
            rhs = tail(nu, nu + n, x)
            cases3 += 1
            if not (lhs > rhs):
                fails3 += 1
                print("FAIL direct-tail", n, nu, r, x, lhs, rhs)
print("direct tail cases:", cases3, "failures:", fails3)

# zero-order boundary: d=0 i.e. nu = 1-n+sqrt(2(1-n)) exactly; check K_1+nu/x K_0 < K_mu
fails4 = 0; cases4 = 0
print("== zero-order boundary comparisons ==")
for (n, nu) in rng:
    if (nu - (1 - n + mp.sqrt(2 * (1 - n)))) != 0:
        continue
    mu = nu + n
    for x in xs + [mp.mpf(100)]:
        c = mp.besselk(1, x) + nu / x * mp.besselk(0, x) < mp.besselk(mu, x)
        cases4 += 1
        if not c:
            fails4 += 1
            print("FAIL zero-order", n, nu, x)
print("zero-order cases:", cases4, "failures:", fails4)
print("DONE")
