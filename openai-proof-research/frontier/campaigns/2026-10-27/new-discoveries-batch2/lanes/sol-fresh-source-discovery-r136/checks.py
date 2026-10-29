import math,json
from pathlib import Path
import mpmath as mp
mp.mp.dps=40
L=Path(__file__).resolve().parent
def run(theta,m,a):
 ts=[]
 for i in range(1,m):
  lo=0.;hi=1.
  for _ in range(55):
   u=(lo+hi)/2;f=u+a*u*(1-u)*(2*u-1)
   if f<i/m:lo=u
   else:hi=u
  ts.append(round((lo+hi)/2,6))
 def C(u,v):return -math.log1p(-math.expm1(-theta*u)*math.expm1(-theta*v)/(-math.expm1(-theta)))/theta
 cov=sum(C(u,v)-u*v for u in ts for v in ts)
 var=sum(min(u,v)-u*v for u in ts for v in ts)
 d1=mp.quad(lambda t:t/mp.expm1(t),[0,theta])/theta
 d2=2*mp.quad(lambda t:t*t/mp.expm1(t),[0,theta])/theta**2
 rho=float(1-12/theta*(d1-d2))
 return dict(theta=theta,m=m,a=a,rho=rho,ordinal=cov/var,gain=cov/var-rho,thresholds=ts)
rows=[run(t,m,a) for t in [2,4,8] for m in [20,50,100] for a in [.1,.3,.5]]
(L/'check-results.json').write_text(json.dumps(rows,indent=2)+'\n')
print(sorted(rows,key=lambda x:x['gain'],reverse=True)[:2])
