from fractions import Fraction as F
from math import isqrt
import sympy as s
from pathlib import Path
P=Path(__file__).parent
# Rational intervals; no floating arithmetic in the sign certificate.
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def mul(a,b):
 v=[x*y for x in a for y in b];return min(v),max(v)
def scale(a,k):return mul(a,(k,k))
def sqrtI(n):
 d=10**18;q=isqrt(n*d*d);assert q*q<n*d*d<(q+1)**2
 return F(q,d),F(q+1,d)
def atanI(q,N=32):
 v=sum(((-1)**k*F(1,(2*k+1)*q**(2*k+1)) for k in range(N)),F(0));w=v+(-1)**N*F(1,(2*N+1)*q**(2*N+1));return min(v,w),max(v,w)
pi=add(scale(atanI(5),F(16)),scale(atanI(239),F(-4)))
assert pi[0]>F(3141592653589793,10**15) and pi[1]<F(3141592653589794,10**15)
a,b=sqrtI(14),sqrtI(7)
H=add(add(scale(mul(a,pi),-F(266733,590359)),scale(mul(b,pi),F(2700,53669))),add(scale(a,F(308016,1341725)),scale(b,F(875664,590359))))
assert H[1]<-F(1,10)
# Independent exact Taylor reconstruction of f and g at c=5/6,z=14/11.
# Differentiate in c by using series of u=sqrt(1-c²), D and atan around 1.
e=s.symbols('e'); cc=s.Rational(5,6);zz=s.Rational(14,11)
tr=lambda x:s.series(x,e,0,3).removeO().expand()
u=tr(s.sqrt(1-(cc+e)**2));D=tr(s.sqrt(1+zz-zz*(cc+e)**2));C=s.sqrt(1+zz)
t=tr(C*u/(cc+e)-1);at=s.pi/4+t/2-tr(t*t)/4
g=tr(2*s.sqrt(zz*(1+zz))*(cc+e)+s.sqrt(zz)*u*at)
f=tr(zz*(cc+e)+D-1)
fcc=2*f.coeff(e,2);gcc=2*g.coeff(e,2)
assert s.simplify(fcc+zz*(1+zz)/(1+zz-zz*cc*cc)**s.Rational(3,2))==0
# z derivatives independently at fixed c; expand in z instead.
zv=zz+e;Du=s.sqrt(1+zv-zv*cc*cc)
fz=s.diff(zv*cc+Du-1,e).subs(e,0)
gz=s.diff(2*s.sqrt(zv*(1+zv))*cc+s.sqrt(zv)*s.sqrt(1-cc*cc)*s.atan(s.sqrt(1+zv)*s.sqrt(1-cc*cc)/cc),e).subs(e,0)
expected=-s.Rational(266733,590359)*s.sqrt(14)*s.pi+s.Rational(2700,53669)*s.sqrt(7)*s.pi+s.Rational(308016,1341725)*s.sqrt(14)+s.Rational(875664,590359)*s.sqrt(7)
assert s.simplify(gcc-gz*fcc/fz-expected)==0
# Area radius adjustment z(e)=z0-fcc/(2fz)e²+O(e4).
assert fz>0
print('PASS independent Taylor reconstruction, exact constrained Hessian, rational H < -1/10')
print('H rational enclosure:',H)
print('No global minimizer or source question resolution follows.')
