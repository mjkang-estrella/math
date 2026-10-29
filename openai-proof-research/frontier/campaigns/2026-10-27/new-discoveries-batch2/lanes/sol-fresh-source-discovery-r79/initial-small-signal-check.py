from fractions import Fraction as F
import math,json
from scipy.integrate import quad
from scipy.special import ndtr
c=F(-4999,10000); beta=F(1,100); lam=F(1,20)
v=(1-c)*(1+2*c)/(1+c)
assert 1+2*c>0 and v<F(3,5000)
I=1-v/lam**2
lower=F(1,2)*F(7,60)*F(19,25)
upper=F(101,100)**3/27
assert lower==F(133,3000) and lower>upper
# Exact derivative factorization: max_y y^2(A-2y)=A^3/27, A=1+beta.
# Difference factors (A-3y)^2(A+6y)/27.
for y in [F(j,100) for j in range(101)]:
 A=1+beta
 assert A**3/27-y*y*(A-2*y)==(A-3*y)**2*(A+6*y)/27
cf=float(c); b=float(beta); l=float(lam); sd=math.sqrt(float(v))
def joint(h,r):
 f=lambda x: math.exp(-x*x/2)/math.sqrt(2*math.pi)*ndtr((h-r*x)/math.sqrt(1-r*r))
 return quad(f,-12,h,epsabs=1e-12)[0]
hm=b*math.sqrt(1-cf*cf)-l*math.sqrt((1+cf)/(1-cf))
hp=b*math.sqrt(1-cf*cf)-l*math.sqrt((1-cf)/(1+cf))
Im=ndtr(l/sd)-ndtr(-l/sd)
mu=l*2*cf/(1+cf)
Ip=ndtr((l-mu)/sd)-ndtr((-l-mu)/sd)
val=(joint(hm,cf)*Im+joint(hp,-cf)*Ip)/2
print(json.dumps(dict(c=str(c),beta=str(beta),lam=str(lam),schur_variance=str(v),I_chebyshev=str(I),certified_lower=str(lower),uniform_orthogonal_upper=str(upper),gap=str(lower-upper),diagnostic_probability=val,diagnostic_mixed_S=joint(hm,cf),diagnostic_mixed_I=Im),indent=2))
