from mpmath import mp, mpf, besselk, quad, sqrt, exp, inf, pi
mp.dps = 50
def delta_of(n, nu):
    mu = nu + n; r = mu*mu - 2*nu - 1
    if abs(r) < mpf("1e-9")*abs(mu*mu): r = mpf(0)
    return mu, sqrt(r)
for (n, nu) in [(0.3, 3.4), (-2.0, 5.4)]:
    mu, d = delta_of(mpf(n), mpf(nu)); eta = d+1
    pred = sqrt(pi/2)*(d*d-eta*eta)/2
    for x in [mpf(80), mpf(200), mpf(500)]:
        lhs = quad(lambda t: t**(-nu)*besselk(mu,t), [x, inf]) - x**(-nu)*besselk(eta, x)
        got = lhs*x**(nu+mpf("1.5"))*exp(x)
        print(f"n={n} nu={nu} x={x}: rel_err={float(abs(got-pred)/abs(pred)):.4%}")
