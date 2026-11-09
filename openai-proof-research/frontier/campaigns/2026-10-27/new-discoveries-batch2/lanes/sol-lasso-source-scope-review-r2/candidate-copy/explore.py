import math,json
from scipy.integrate import quad
from scipy.special import ndtr
from scipy.optimize import minimize_scalar
c=-.4999
v=(1-c)*(1+2*c)/(1+c)
def joint(h,r):
 return quad(lambda x:math.exp(-x*x/2)/math.sqrt(2*math.pi)*ndtr((h-r*x)/math.sqrt(1-r*r)),-12,h,epsabs=1e-10)[0]
for b in [.01,.2,.5,1,1.5,2,3]:
 f=lambda l:ndtr(b-l)**2*(2*ndtr(l)-1)
 opt=minimize_scalar(lambda l:-f(l),bounds=(0,b+4),method='bounded')
 l=.05
 hm=b*math.sqrt(1-c*c)-l*math.sqrt((1+c)/(1-c))
 val=joint(hm,c)*(2*ndtr(l/math.sqrt(v))-1)/2
 print(json.dumps(dict(beta=b,orthogonal_opt=-opt.fun,lambda_opt=opt.x,candidate_lower_mixed=val)))
