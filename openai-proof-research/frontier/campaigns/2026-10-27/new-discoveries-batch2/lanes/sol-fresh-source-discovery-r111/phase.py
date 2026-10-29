import math,json
from scipy.integrate import quad
from scipy.special import gammaln
for p in [.5,.6,.65,.7,.75,.8,.9,1.1]:
 u=math.log(2/(p+1))/(1-p);e=(gammaln(p+1)-p*math.log(p))/(1-p)
 best=(-1,None)
 for a in [.05,.1,.2,.5,1,2,3,4,6,8,12,20,40]:
  c=1/(-math.expm1(-a))
  I=c**p*(-math.expm1(-p*a))/p
  A,err1=quad(lambda s:(c*c*math.exp(-s)*s)**p,0,a,epsabs=1e-10)
  B,err2=quad(lambda s:(c*c*math.exp(-s)*(2*a-s))**p,a,2*a,epsabs=1e-10)
  increment=math.log((A+B)/I)/(1-p)
  if increment>best[0]:best=(increment,a)
 print(json.dumps({'p':p,'uniform':u,'exponential':e,'best_truncated':best,'margin':best[0]-max(u,e),'status':'nonrigorous diagnostic'}))
