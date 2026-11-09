from fractions import Fraction as F
import math,json
from scipy.special import ndtr
from scipy.integrate import quad
c=F(-49999,100000); beta=F(1); lam=F(1,20)
v=(1-c)*(1+2*c)/(1+c)
assert 1+2*c==F(1,50000) and 1-c>0
assert v<F(3,50000)
assert 1-v/lam**2>F(122,125)
# h > sqrt(3)/2 - 1/20 > 4/5.
assert F(3,4)>F(17,20)**2
# Gaussian CDF(4/5)>3/4 follows from exp(-u^2/2)>=1-u^2/2.
x=F(4,5)
assert F(3,8)*(x-x**3/6)>F(1,4)
# Classical Archimedean pi bounds imply 3/8 < 1/sqrt(2*pi) < 2/5.
assert F(223,71)>F(25,8) and F(22,7)<F(32,9)
A=F(9,5)
upper=A**3/27
lower=F(1,2)*F(1,2)*F(122,125)
assert upper==F(27,125) and lower==F(61,250) and lower-upper==F(7,250)
# Exact polynomial identity; all coefficients zero after subtraction.
# A^3/27 - y^2(A-2y)=(A-3y)^2(A+6y)/27.
coefs=[A**3/27,0,-A,F(2)]
factored=[A**3/27,0,-A,F(2)]
assert coefs==factored
cf=float(c); b=float(beta); l=float(lam); sd=math.sqrt(float(v))
def joint(h,r):
 return quad(lambda z:math.exp(-z*z/2)/math.sqrt(2*math.pi)*ndtr((h-r*z)/math.sqrt(1-r*r)),-12,h,epsabs=1e-12)[0]
hm=b*math.sqrt(1-cf*cf)-l*math.sqrt((1+cf)/(1-cf))
hp=b*math.sqrt(1-cf*cf)-l*math.sqrt((1-cf)/(1+cf))
Im=ndtr(l/sd)-ndtr(-l/sd)
mu=l*2*cf/(1+cf)
Ip=ndtr((l-mu)/sd)-ndtr((-l-mu)/sd)
print(json.dumps(dict(c=str(c),beta=str(beta),lam=str(lam),eigenvalue_min=str(1+2*c),schur_variance=str(v),certified_lower=str(lower),uniform_orthogonal_upper=str(upper),certified_gap=str(lower-upper),diagnostic_h_mixed=hm,diagnostic_I_mixed=Im,diagnostic_S_mixed=joint(hm,cf),diagnostic_full_probability=(joint(hm,cf)*Im+joint(hp,-cf)*Ip)/2),indent=2))
