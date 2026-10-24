"""Bounded floating-point exploration only; no certified inequality or geometric proof."""
import math,json
from pathlib import Path
R=Path(__file__).resolve().parent
c=1/(1+.400682721856639)
def series(a,N=24):
 g=[1.,a];h=[1.,-a]
 for k in range(2,N+1):
  rhs=.5*((1/c-1) if k==2 else -h[k-2])
  g.append(rhs/((k-1)*(k+9)*(k+10)))
  h.append(-sum(g[j]*h[k-j] for j in range(1,k+1)))
 return g
def shoot(a,Y=30.,step=.0015):
 y0=.005;g=series(a);z=[sum((k**j if j else 1)*v*y0**k for k,v in enumerate(g)) for j in range(3)]
 t=math.log(y0);end=math.log(Y);N=math.ceil((end-t)/step);dt=(end-t)/N
 low=1.;maxup=0.;mind=-a
 def fun(t,z):
  G,P,Q=z
  if G<=.02: raise ArithmeticError()
  return [P,Q,-18*Q-71*P+90*(G-1)+math.exp(2*t)*.5*(1/c-1/G)]
 try:
  for i in range(N):
   k1=fun(t,z);k2=fun(t+dt/2,[v+dt*w/2 for v,w in zip(z,k1)])
   k3=fun(t+dt/2,[v+dt*w/2 for v,w in zip(z,k2)]);k4=fun(t+dt,[v+dt*w for v,w in zip(z,k3)])
   z=[v+dt*(p+2*q+2*u+w)/6 for v,p,q,u,w in zip(z,k1,k2,k3,k4)];t+=dt
   low=min(low,z[0]);maxup=max(maxup,z[1])
   if not all(math.isfinite(v) for v in z) or abs(z[0])>20:return {'a':a,'exit':'large','y':math.exp(t),'z':z}
  return {'a':a,'exit':'end','y':Y,'z':z,'minG':low,'maxDG':maxup}
 except ArithmeticError:return {'a':a,'exit':'small','y':math.exp(t),'z':z}
if __name__=='__main__':
 rows=[shoot(-k/1000,Y=20) for k in [1,5,10,20,30,40,50,70,100,130,160]]
 out={'status':'floating exploration only','c':c,'Y':20,'rows':rows}
 (R/'private/forward-exploration.json').write_text(json.dumps(out,indent=2))
 print(json.dumps(out,indent=2))
