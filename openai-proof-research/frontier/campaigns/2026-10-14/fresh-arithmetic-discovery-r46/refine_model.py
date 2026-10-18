#!/usr/bin/env python3
"""MIT. Floating exploratory weighted-arc integration; no proof certificate."""
import math,json

def endpoint(lam,kap,t,sgn,step):
 y=lam*t+kap*t*t/2;u=t
 def f(v,z):return (lam*z+kap*z*z/2-v)/(1+2*z)
 def advance(y,u,dt):
  k1=f(y,u);k2=f(y+dt/2,u+dt*k1/2);k3=f(y+dt/2,u+dt*k2/2);k4=f(y+dt,u+dt*k3)
  return u+dt*(k1+2*k2+2*k3+k4)/6
 for j in range(2000000):
  dt=sgn*step;un=advance(y,u,dt)
  if un<=0:
   lo=0.;hi=1.
   for _ in range(40):
    mid=(lo+hi)/2
    if advance(y,u,dt*mid)>0:lo=mid
    else:hi=mid
   return y+dt*(lo+hi)/2
  y,u=y+dt,un
 raise ValueError('endpoint timeout')
def data(lam,kap,t,step):
 a=endpoint(lam,kap,t,-1,step);b=endpoint(lam,kap,t,1,step)
 return (b-a)/2,(a+b)/2

def H(lam,kap,r,step):
 lo=0.;hi=1.
 while data(lam,kap,hi,step)[0]<r:
  hi*=2
  if hi>64:raise ValueError('peak bracket limit')
 for i in range(43):
  mid=(lo+hi)/2
  if data(lam,kap,mid,step)[0]<r:lo=mid
  else:hi=mid
 return data(lam,kap,(lo+hi)/2,step)[1]
def C(lam,kap,r,step,eps=.015):
 def PQ(z):return ((H(lam+eps,kap,z,step)-H(lam-eps,kap,z,step))/(2*eps),(H(lam,kap+eps,z,step)-H(lam,kap-eps,z,step))/(2*eps))
 P,Q=PQ(r);pp,qp=PQ(r+eps);pm,qm=PQ(r-eps);R=(pp-pm)/(2*eps);S=(qp-qm)/(2*eps);G=P*S-Q*R
 return R/G,G
for lam,kap,r in [(0,0,8),(0,4,2),(2,1,4)]:
 for step,eps in [(.002,.025),(.001,.015),(.0005,.01)]:
  dr=.02
  a,g=C(lam,kap,r-dr,step,eps);b,_=C(lam,kap,r+dr,step,eps)
  print(json.dumps(dict(lam=lam,kap=kap,r=r,step=step,eps=eps,C_r_est=(b-a)/(2*dr),G=g)),flush=True)
