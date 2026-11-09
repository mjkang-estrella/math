# High-precision constants for the 344302 asymptotic proof (diagnostic; rigorous bounds in dd_rigorous.py).
import sys
sys.path.append('/home/mj-kang/.local/lib/python3.14/site-packages')
import mpmath as mp
from math import factorial
mp.mp.dps = 50
sys.path.insert(0, sys.argv[1])
from dd344302 import dd_single
x0 = 2*mp.pi/(3*mp.sqrt(3))
c = lambda s: (1, -1, 0)[s % 3]
def T(x, y, M=80):
    return mp.fsum(c(s)*c(t)*mp.power(x, s)*mp.power(y, t)/mp.factorial(s+t+3) for s in range(M) for t in range(M))
e0 = mp.e**(x0/2)/x0; em1 = mp.e**(-x0)/(2*x0)
tau = e0*em1*T(-2*x0, x0)
print('x0', x0, 'e0', e0, 'e-1', em1, 'T(-2x0,x0)', T(-2*x0, x0), 'tau', tau)
NA = 60
a = [mp.mpf(dd_single(L, -1) if L else 1)/mp.factorial(L) for L in range(NA)]
# check a_L asymptotics
for L in (10, 20, 40):
    print('a_L/(e0 x0^-L) - 1 at L=%d:' % L, a[L]/(e0*x0**(-L)) - 1, ' predicted -1 mode:', (em1/e0)*(-mp.mpf(1)/2)**L)
def W(p, z):
    return mp.fsum(a[p-s]*c(s)*mp.fsum(c(t)*mp.power(z, t)/mp.factorial(s+t+3) for t in range(80)) for s in range(p+1))
for p in range(0, 16):
    U = W(p, x0) - x0*W(p+1, x0)
    norm = e0*U*x0**p
    pred = mp.mpf(3)/2*tau*(-mp.mpf(1)/2)**p
    print('p', p, 'e0*x0^p*U_p(x0) = %s' % mp.nstr(norm, 12), ' main (3/2)tau(-1/2)^p = %s' % mp.nstr(pred, 12), ' ratio', mp.nstr(norm/pred, 10))
