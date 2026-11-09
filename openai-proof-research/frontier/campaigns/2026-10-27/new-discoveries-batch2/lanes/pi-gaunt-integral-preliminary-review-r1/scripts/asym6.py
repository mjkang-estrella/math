import numpy as np
from scipy.integrate import quad
from scipy.special import kve
n, nu = 0.3, 3.4
mu = nu+n; d = (mu*mu-2*nu-1)**0.5; eta = d+1
alpha = nu+0.5
a = (4*mu*mu-1)/8; b = (4*mu*mu-1)*(4*mu*mu-9)/128
c1T = a-alpha; c2T = alpha*(alpha+1)-a*(alpha+1)+b
ap = (4*eta*eta-1)/8
print(f"c1T={c1T:.6f} c2T={c2T:.6f}  c1K={ap:.6f}")
for x in [20., 40., 80., 160., 320., 640.]:
    # T*e^x*x^nu = int_0^inf e^-s (x/(x+s))^nu kve(mu, x+s) ds
    T_scaled, err = quad(lambda s: np.exp(-s)*(x/(x+s))**nu*kve(mu, x+s), 0, np.inf, epsabs=1e-13, epsrel=1e-13, limit=400)
    # S = sqrt(pi/2) e^-x x^-alpha  => T/S = T_scaled*x^nu*x^alpha/sqrt(pi/2)/1? T = e^-x*T_scaled
    TS = T_scaled*x**(nu+alpha)/np.sqrt(np.pi/2)
    r = (TS - 1 - c1T/x)*x*x
    K = x**(-nu)*kve(eta,x)*np.exp(-x)  # x^-nu K_eta(x)
    KS = K/ (np.sqrt(np.pi/2)*np.exp(-x)*x**(-alpha))
    rK = (KS-1-ap/x)*x*x
    print(f"x={x:6.0f}  T_resid={r:10.4f} (want {c2T:.3f})   K_resid={rK:10.4f} (want {4*eta*eta*eta*eta-4*eta*eta-9:(0}')" if False else f"x={x:6.0f}  T_resid={r:10.4f} (want {c2T:.3f})   K_resid={rK:10.4f} (want {(4*eta**2-1)*(4*eta**2-9)/128:.3f})")
