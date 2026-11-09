from mpmath import mp, mpf, besselk, quad, sqrt, exp, inf, pi
mp.dps = 60
n, nu = mpf("0.3"), mpf("3.4")
mu = nu+n; d = sqrt(mu*mu-2*nu-1); eta = d+1
alpha = nu+mpf("0.5")
S = lambda x: sqrt(pi/2)*exp(-x)*x**(-alpha)
# c1 = (4d^2-1)/8; c2 from sympy: compute numerically here
mu2 = mu*mu; a=(4*mu2-1)/8; b=(4*mu2-1)*(4*mu2-9)/128
c1T = a-alpha; c2T = alpha*(alpha+1)-a*(alpha+1)+b
ap=(4*eta*eta-1)/8; bp=(4*eta*eta-1)*(4*eta*eta-9)/128
for x in [mpf(60), mpf(120), mpf(240), mpf(480), mpf(960)]:
    T = quad(lambda t: t**(-nu)*besselk(mu,t), [x, inf])
    K = x**(-nu)*besselk(eta, x)
    rT = (T/S(x)-1 - c1T/x)*x*x
    rK = (K/S(x)-1 - ap/x)*x*x
    print(f"x={x}: T resid*c2-fit={float(rT):.4f} (c2T={float(c2T):.4f})  K resid={float(rK):.4f} (c2K={float(bp):.4f})")
