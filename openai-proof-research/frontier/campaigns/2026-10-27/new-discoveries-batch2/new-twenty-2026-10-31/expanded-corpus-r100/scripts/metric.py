import numpy as np,json
from scipy.optimize import minimize_scalar
rng=np.random.default_rng(347800)
def equal_s(k,r):
 # conjugate pair k+-ir: Theorem 2.6 piecewise value
 if k*k+r*r>=k:return (k*k+r*r)**.5
 return r/((1-k)**2+r*r)**.5
best=[1,1,1];arg=[None]*3;tested=[0]*3
for i in range(100000):
 q,t=rng.random(2);theta=rng.random()*np.pi
 z=t*np.exp(1j*theta);x=(q+z)/(1+q*z);y=(q-z)/(1-q*z)
 k=abs(x+y)/2;r=abs(x-y)/2
 u=q*(1+t*t)/(1+q*q*t*t);v=t*(1-q*q)/(1+q*q*t*t)
 s2=equal_s(u,v);s0=equal_s(k,r);s3=(1+q)*t/(1+q*t*t)
 point=abs(x-y)/(abs(x-y)**2+4*(1-abs(x))*(1-abs(y)))**.5
 dif=[s2-s0,None,s3 and point-s3]
 if k+r<1:dif[1]=r/(1-k)-s3
 for j,d in enumerate(dif):
  if d is not None:
   tested[j]+=1
   if d<best[j]:best[j]=float(d);arg[j]=[float(q),float(t),float(theta)]
print(dict(samples=100000,tested=tested,minimum_slacks=best,args=arg),flush=True)
json.dump(dict(samples=100000,tested=tested,minimum_slacks=best,args=arg,method='hyperbolic parameters q,t,theta; source Theorems 2.6,5.3,5.12'),open('outputs/metric.json','w'),indent=2)
