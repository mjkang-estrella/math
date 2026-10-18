#!/usr/bin/env python3
"""MIT. Exact finite rational controls, not proofs of global ODE signs."""
from fractions import Fraction as F
import itertools,json

def require(value,label):
 if not value:raise ValueError(label)

count=0
for a,beta,u,lam,kap,d in itertools.product([F(1,3),F(1),F(3)],[F(0),F(1,2),F(2)],[F(0),F(1,5),F(1),F(4)],[F(-2),F(0),F(3)],[F(-3),F(0),F(2)],[F(1,7),F(1),F(3)]):
 w=a+2*beta*u;v=a*u+beta*u*u;b=a*kap-2*beta*lam
 require(w*w==a*a+4*beta*v,'energy denominator')
 require((kap*w-2*beta*(lam+kap*u))/w**3==b/w**3,'profile second derivative')
 require((w-2*beta*(u-d))/w**3==(a+2*beta*d)/w**3,'forcing second derivative')
 require((a+2*beta*d)/w**3>0,'strict forcing convexity')
 require(a+2*beta*d>=a>0,'b derivative')
 vmax=v+1
 require(w**6<=(a*a+4*beta*vmax)**3,'curvature denominator bound')
 count+=6
# At a=1,beta=lambda=kappa=0,r=1: u=(1-y^2)/2, d=1/5.
# f=(1-6y^2+5y^4)/40; z=y(1-y^2)^2/40.
f={0:F(1,40),2:F(-6,40),4:F(5,40)}
z={1:F(1,40),3:F(-2,40),5:F(1,40)}
require({n-1:n*c for n,c in z.items()}==f,'anchor z derivative')
require(sum(z.values())==0 and sum(c*(-1)**n for n,c in z.items())==0,'fixed endpoints')
require(sum(c*F(2,n+1) for n,c in f.items())==0,'centering')
for y in [F(-3,4),F(-1,4),F(1,4),F(3,4)]:
 require(sum(c*y**n for n,c in z.items())*y>0,'anchor crossing')
require((F(2,3)-F(2,5))/2==F(2,15),'anchor slope derivative')
print(json.dumps({'status':'PASS','rational_parameter_controls':count,'anchor_controls':8,'dependencies':'Python standard library fractions; no numerical integration','scope':'finite identity controls, not global uniqueness or W proof'},indent=2))
