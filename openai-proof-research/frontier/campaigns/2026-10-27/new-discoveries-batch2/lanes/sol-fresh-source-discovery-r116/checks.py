from fractions import Fraction as Q
from pathlib import Path
import json,math,random,time
L=Path(__file__).resolve().parent
def f(t):return min(t*t,t)
def P(v):
 s=sum((f(x)/10 for x in v),Q(0));assert s>=1
 return s
x=(Q(1,2),Q(100));y=(Q(10),Q(0));xy=tuple(a+b for a,b in zip(x,y))
assert P(xy)-P(x)-P(y)==Q(1,40)
assert f(Q(1))>(f(Q(3,4))+f(Q(5,4)))/2
def rat(t):return t*t/(1+t)-Q(1,1000)*t*t/(1+t)**2/(1+10000*(t-2)**2)
t=Q(201,100);q=t*t/(1+t)**2;qp=2*t/(1+t)**3;qpp=2*(1-2*t)/(1+t)**4
u=t-2;v=1+10000*u*u;R=1/v;Rp=-20000*u/v**2;Rpp=(600000000*u*u-20000)/v**3
fpp=2/(1+t)**3-Q(1,1000)*(qpp*R+2*qp*Rp+q*Rpp)
assert fpp<0
# Floating exploratory screen only. Bisection is not interval arithmetic.
def rf(t):return t*t/(1+t)-.001*t*t/(1+t)**2/(1+10000*(t-2)**2)
def inv(s):
 # rf lies between f0-.001 and f0, where inv(f0)(s)=(s+sqrt(s*s+4*s))/2.
 lo=(s+math.sqrt(s*s+4*s))/2;hi=(s+.001+math.sqrt((s+.001)**2+4*(s+.001)))/2
 for _ in range(42):
  m=(lo+hi)/2
  if rf(m)<s:lo=m
  else:hi=m
 return (lo+hi)/2
random.seed(116);rows=[]
for a,b in ((.1,.1),(2.,2.),(.01,.2)):
 def pp(v):return inv(a*rf(v[0])+b*rf(v[1]))
 worst=(-1e100,None)
 for _ in range(12000):
  v=tuple(10**random.uniform(-3,3) for _ in range(2));w=tuple(10**random.uniform(-3,3) for _ in range(2))
  gap=pp((v[0]+w[0],v[1]+w[1]))-pp(v)-pp(w)
  if gap>worst[0]:worst=(gap,(v,w))
 rows.append({'weights':[a,b],'samples':12000,'largest_subadditivity_defect_float':worst[0],'witness_float':worst[1],'status':'NUMERICAL_ONLY'})
out={'exact_piecewise_failed_candidate':{'x':list(map(str,x)),'y':list(map(str,y)),'P_x':str(P(x)),'P_y':str(P(y)),'P_x_plus_y':str(P(xy)),'defect':str(P(xy)-P(x)-P(y))},'smooth_candidate_second_derivative_at_201_over_100':str(fpp),'smooth_exploration':rows,'warning':'No finite check establishes source universal subadditivity or refutes the source conjecture.'}
(L/'exact-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
