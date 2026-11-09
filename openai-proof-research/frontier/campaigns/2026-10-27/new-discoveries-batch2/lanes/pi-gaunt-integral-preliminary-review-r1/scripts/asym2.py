from mpmath import mp, mpf, besselk, quad, sqrt, exp, inf, pi
mp.dps = 40
n, nu = mpf("0.3"), mpf("3.4")
mu = nu+n; d = sqrt(mu*mu-2*nu-1); eta = d+1
print("mu,d,eta:", mu, d, eta)
alpha = nu+mpf("0.5")
for x in [mpf(80), mpf(200), mpf(500)]:
    T = quad(lambda t: t**(-nu)*besselk(mu,t), [x, inf])
    K = x**(-nu)*besselk(eta, x)
    S = sqrt(pi/2)*exp(-x)*x**(-alpha)
    # normalized coefficients: T/S should be 1 + (d^2-eta^2)/(2x) + ...
    print("x=",x)
    print("  T/S-1       =", (T/S-1))
    print("  pred (d2-e2)/2x =", (d*d-eta*eta)/2/x)
    print("  K/S-1       =", (K/S-1), " pred (4e2-1)/8x =", (4*eta*eta-1)/8/x)
    print("  (T-K)*x^(nu+3/2)*e^x =", (T-K)*x**(nu+mpf("1.5"))*exp(x), " pred:", sqrt(pi/2)*(d*d-eta*eta)/2)
