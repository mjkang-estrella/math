import numpy as np
from mpmath import mp, log, exp
mp.dps=40
a=[0.7,1.3,2.1,0.4,1.0]; n=len(a)
def f(p): return (sum(x**p for x in a))**(-1/p)
def fpp(p,h=mp.mpf('1e-5')): return (f(p+h)-2*f(p)+f(p-h))/h**2
for p in [0.4, 0.6, float(log(5)/2), 1.0, 2.0]:
    p=mp.mpf(str(p))
    Z=sum(x**p for x in a); w=[x**p/Z for x in a]
    H=-sum(wi*log(wi) for wi in w)
    la=[log(x) for x in a]
    m=sum(wi*s for wi,s in zip(w,la)); V=sum(wi*s*s for wi,s in zip(w,la))-m*m
    formula=f(p)/p**4*(H**2-2*p*H-p**3*V)
    print(f"p={float(p):.3f} f'' numeric={float(fpp(p)):.6f} formula={float(formula):.6f} concave={fpp(p)<0} (log(n)/2={float(log(5)/2):.4f})")
