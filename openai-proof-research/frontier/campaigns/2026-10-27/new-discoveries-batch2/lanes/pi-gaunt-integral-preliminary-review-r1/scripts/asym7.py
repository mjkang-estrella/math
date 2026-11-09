import numpy as np
from scipy.integrate import quad
from scipy.special import kve
from mpmath import mp, mpf, besselk, quad as mpquad, sqrt as mpsqrt, exp as mpexp, pi as mppi, inf
mp.dps = 40
n, nu = 0.3, 3.4
mu = nu+n; d = (mu*mu-2*nu-1)**0.5
alpha = nu+0.5
a = (4*mu*mu-1)/8; b = (4*mu*mu-1)*(4*mu*mu-9)/128
c1 = a-alpha; c2 = alpha*(alpha+1)-a*(alpha+1)+b
for x in [20., 40., 80., 160., 320.]:
    Ts, err = quad(lambda s: np.exp(-s)*(x/(x+s))**nu*kve(mu, x+s)*x**nu, 0, np.inf, epsabs=1e-14, epsrel=1e-14, limit=500)
    # Ts = e^x * T  (since (x+s)^-nu = x^-nu (x/(x+s))^nu; multiply by x^nu restores)
    # careful: int e^-s (x+s)^-nu kve ds = e^x T. I wrote (x/(x+s))^nu * x^nu = (x/(x+s))^nu*x^nu... wrong.
    Ts2, err2 = quad(lambda s: np.exp(-s)*kve(mu, x+s)/(x+s)**nu, 0, np.inf, epsabs=1e-300, epsrel=1e-13, limit=500)
    TS1 = Ts*x**alpha/np.sqrt(np.pi/2)
    TS2 = Ts2*x**alpha/np.sqrt(np.pi/2)
    xm = mpf(x)
    Tm = mpquad(lambda t: t**(-mpf(nu))*besselk(mu, t), [xm, inf])
    TSm = float(Tm/(mpsqrt(mppi/2)*mpexp(-xm)*xm**(-mpf(alpha))))
    print(f"x={x:6.0f} TS_scipy1={TS1:.8f} TS_scipy2={TS2:.8f} TS_mpmath={float(TSm):.8f}")
    print(f"          resid1={(TS1-1-c1/x)*x*x:12.4f} resid2={(TS2-1-c1/x)*x*x:12.4f} residm={(float(TSm)-1-c1/x)*x*x:12.4f}  (want {c2:.4f})")
