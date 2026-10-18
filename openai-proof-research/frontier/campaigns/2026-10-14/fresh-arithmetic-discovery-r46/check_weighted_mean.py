#!/usr/bin/env python3
"""MIT. Exact finite weighted-mean controls, not quadrature or a proof substitute."""
from fractions import Fraction as F
import json
checks=0
def require(v,label):
 global checks
 if not v:raise ValueError(label)
 checks+=1
for a in [F(1,2),F(1),F(2)]:
 for beta in [F(0),F(1,2),F(1),F(2)]:
  for weights in [[F(1,3)]*3,[F(1,2),F(1,4),F(1,4)],[F(1,7),F(2,7),F(4,7)]]:
   r=F(4);us=[F(1,8),F(1,4),F(1,2)]
   ur=[2*u*(a+beta*u)/(r*(a+2*beta*u)) for u in us]
   logs=[a*a/(r*(a+2*beta*u)**2) for u in us]
   avg=lambda xs:sum(w*x for w,x in zip(weights,xs))
   P=avg(us);Q=avg([u*u/2 for u in us]);R=avg(ur);S=avg([u*v for u,v in zip(us,ur)])
   Rr=avg([v*l for v,l in zip(ur,logs)]);Sr=avg([v*v+u*v*l for u,v,l in zip(us,ur,logs)])
   G=P*S-Q*R;W=R*Sr-S*Rr;T=S/R;Tp=W/(R*R)
   require(G>0,'positive determinant')
   require(Tp>0 and -P*W/(G*G)<0,'weighted mean and ratio signs')
   pw=[w*v/R for w,v in zip(weights,ur)]
   exact=sum(w*v for w,v in zip(pw,ur))+sum(w*u*l for w,u,l in zip(pw,us,logs))-T*sum(w*l for w,l in zip(pw,logs))
   require(Tp==exact,'weighted differentiation identity')
   for u,v,l in zip(us,ur,logs):
    require(u/r<v<=2*u/r and 0<l<=1/r,'pointwise bounds')
    c=2*u*(a+beta*u)/(r*r)
    require(0<c<1 and l==a*a/(r*(a*a+2*beta*r*r*c)),'energy-log identity')
print(json.dumps({'status':'PASS_EXACT_FINITE_CONTROLS','checks':checks,'discrete_measures':36}))
