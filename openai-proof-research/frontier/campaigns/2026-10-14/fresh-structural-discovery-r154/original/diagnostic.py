"""Bounded exact checks of r154 coordinate formulas; not mathematical gates."""
from fractions import Fraction as F
from itertools import combinations,product
from math import factorial
from collections import defaultdict
import json

def prod(xs):
 out=F(1)
 for x in xs: out*=x
 return out

def check(c,R,t):
 C=sum(c); groups=[]
 for i,ci in enumerate(c): groups += [i]*ci
 U=frozenset(range(C)); z=[F(i+2) for i in range(len(c))]
 def occupancy(S): return tuple(sum(groups[u]==i for u in S) for i in range(len(c)))
 def mu(x): return F(1,2**sum(v*v for v in x)) if sum(x)==R and all(0<=v<=ci for v,ci in zip(x,c)) else F(0)
 def nu(x): return F(1,3**sum(v*v for v in x)) if sum(x)==R and all(0<=v<=ci for v,ci in zip(x,c)) else F(0)
 def mh(x): return mu(x)*prod(F(factorial(ci-v),factorial(ci)) for v,ci in zip(x,c))
 def nh(y): return nu(tuple(ci-v for v,ci in zip(y,c)))*prod(F(factorial(ci-v),factorial(ci)) for v,ci in zip(y,c))
 def key(S,T): return occupancy(S),occupancy(T),occupancy(S&T)
 def weight(S,T):
  x,y,h=key(S,T)
  return mh(x)*nh(y)*t**sum(h)*prod(z[i]**(x[i]+y[i]) for i in range(len(c)))
 states=[(frozenset(S),frozenset(T)) for S in combinations(U,R) for T in combinations(U,C-R)]
 masses=defaultdict(F); reps={}
 for S,T in states:
  k=key(S,T);masses[k]+=weight(S,T);reps[k]=(S,T)
 for (x,y,h),mass in masses.items():
  expected=mu(x)*nu(tuple(ci-v for v,ci in zip(y,c)))
  for i,ci in enumerate(c):
   counts=[h[i],x[i]-h[i],y[i]-h[i],ci-x[i]-y[i]+h[i]]
   expected*=F(factorial(ci),prod(factorial(v) for v in counts))*F(factorial(ci-x[i])*factorial(ci-y[i]),factorial(ci)**2)*t**h[i]*z[i]**(x[i]+y[i])
  assert mass==expected
 targets=sum((mass for (x,y,h),mass in masses.items() if all(yi==ci-xi for xi,yi,ci in zip(x,y,c)) and not any(h)),F())
 Z=sum((mu(x)*nu(x) for x in product(*(range(ci+1) for ci in c))),F())
 assert targets==Z*prod(z[i]**ci/F(factorial(ci)) for i,ci in enumerate(c))
 comparisons=0
 for S,T in states:
  x,y,h=key(S,T); direct=defaultdict(F)
  for u in S:
   S0=S-{u}; xx=occupancy(S0)
   D=sum((z[groups[v]]*mh(occupancy(S0|{v})) for v in U-S0),F())
   for v in U-S0:
    direct[key(S0|{v},T)]+=t**(-int(u in T))*z[groups[v]]*mh(occupancy(S0|{v}))/D
  lump=defaultdict(F)
  for i in range(len(c)):
   for b in [0,1]:
    multiplicity=h[i] if b else x[i]-h[i]
    if not multiplicity: continue
    xx=list(x);hh=list(h);xx[i]-=1;hh[i]-=b
    D=sum(((c[j]-xx[j])*z[j]*mh(tuple(xx[k]+int(k==j) for k in range(len(c)))) for j in range(len(c))),F())
    for j in range(len(c)):
     for bp in [0,1]:
      available=(y[j]-hh[j]) if bp else (c[j]-xx[j]-y[j]+hh[j])
      if not available: continue
      xxx=tuple(xx[k]+int(k==j) for k in range(len(c)));hhh=tuple(hh[k]+bp*int(k==j) for k in range(len(c)))
      lump[(xxx,y,hhh)]+=multiplicity*t**(-b)*available*z[j]*mh(xxx)/D
  assert dict(direct)==dict(lump)
  comparisons+=len(direct)
 return len(states),len(masses),comparisons

out={'cases':[]}
for c in [(1,2),(2,2),(2,3),(3,3)]:
 for t in [F(1,2),F(1,5)]:
  v=check(c,sum(c)//2,t);out['cases'].append({'capacities':c,'t':str(t),'states':v[0],'orbits':v[1],'rate_comparisons':v[2]})
# Signature illustration: two positive directions and a negative orthogonal one.
Q=[[F(1,4),F(1),F(4)],[F(1),F(1),F(1)],[F(4),F(1),F(1,4)]]
def bil(u,v): return sum((u[i]*Q[i][j]*v[j] for i in range(3) for j in range(3)),F())
u=[1,0,1];v=[0,1,0];w=[1,0,-1]
assert bil(u,u)==F(17,2) and bil(u,v)==2 and bil(v,v)==1
assert bil(u,u)*bil(v,v)-bil(u,v)**2==F(9,2)
assert bil(w,w)==F(-15,2) and bil(w,u)==bil(w,v)==0
out['signature']={'positive_plane_determinant':'9/2','negative_square':'-15/2'}
print(json.dumps(out,indent=2))
