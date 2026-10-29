import mpmath as m,json
from fractions import Fraction as F
m.mp.dps=40
# Rational arithmetic in Q(i), independent of candidate checker.
def mul(a,b):return(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def div(a,b):
 c=mul(a,(b[0],-b[1]));d=b[0]**2+b[1]**2;return(c[0]/d,c[1]/d)
r=(F(1),F(2));r2=mul(r,r);a=div((1+r2[0],r2[1]),(4+r2[0],r2[1]));assert a==(F(14,17),F(12,17));assert a[0]**2+a[1]**2==F(20,17)
# Exact conjugate Bernardi multipliers, sample rational r,n only diagnostics of symbolic identity in review.
for r in [F(0),F(1,5),F(1),F(17,3)]:
 for n in range(1,30):
  z=mul(div((F(1),r),(F(n),r)),div((F(1),-r),(F(n),-r)))
  assert z==((1+r*r)/(n*n+r*r),0)
rows=[]
for r in [m.mpf('.2'),m.mpf('1'),m.mpf('4')]:
 for t in [m.mpf('.4'),m.mpf('1.9'),m.pi]:
  z=m.exp(1j*t)
  g=m.quad(lambda x:m.cos(r*m.log(x))*z/(1-z*x),[0,.5,1])
  dg=m.quad(lambda x:m.cos(r*m.log(x))*z/(1-z*x)**2,[0,.5,1])
  ddg=m.quad(lambda x:m.cos(r*m.log(x))*z*(1+z*x)/(1-z*x)**3,[0,.5,1])
  v=m.pi/2*m.sinh(r*(m.pi-t))/m.sinh(m.pi*r)
  err=abs(g.imag-v);ode=abs(ddg+r*r*g-z/(1-z)**2)
  assert err<m.mpf('1e-30') and ode<m.mpf('1e-29')
  assert (dg/g).real>0
  rows.append(dict(r=str(r),t=str(t),sine_error=str(err),ode_error=str(ode),Re_q=str((dg/g).real)))
print(json.dumps({'exact_complex_obstruction':True,'conjugate_multiplier_checks':True,'boundary_checks':rows,'status':'diagnostics only, not universal proof'},indent=2))
