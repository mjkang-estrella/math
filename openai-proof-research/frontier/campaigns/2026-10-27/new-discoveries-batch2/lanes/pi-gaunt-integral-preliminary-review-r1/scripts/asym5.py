from mpmath import mp, mpf, besselk, quad, sqrt, exp, inf, pi
mp.dps = 40
n, nu = mpf("0.3"), mpf("3.4")
mu = nu+n; d = sqrt(mu*mu-2*nu-1); eta = d+1
alpha = nu+mpf("0.5")
S = lambda x: sqrt(pi/2)*exp(-x)*x**(-alpha)
a=(4*mu*mu-1)/8; b=(4*mu*mu-1)*(4*mu*mu-9)/128
c1T = a-alpha; c2T = alpha*(alpha+1)-a*(alpha+1)+b
def T_sub(x):
    return quad(lambda s: (x+s)**(-nu)*besselk(mu, x+s), [0, inf])
for x in [mpf(60), mpf(240), mpf(960)]:
    T1 = quad(lambda t: t**(-nu)*besselk(mu,t), [x, inf])
    T2 = T_sub(x)
    print(f"x={x}")
    print("  direct resid (want ->%.2f):"%c2T, float((T1/S(x)-1-c1T/x)*x*x))
    print("  subst  resid (want ->%.2f):"%c2T, float((T2/S(x)-1-c1T/x)*x*x))
    print("  rel diff:", float(abs(T1-T2)/T2))
