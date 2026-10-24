"""Exact fixed-point interval certificate for periodic Coulomb energies.
All arithmetic here is integer/rational. No transcendental runtime evaluations.
Run from the project root. Outputs remain under this script's directory.
"""
from pathlib import Path
from fractions import Fraction
from collections import Counter
import json,hashlib,sys
S=10**180
def floorq(a,b): return a//b
def ceilq(a,b): return -((-a)//b)
class I:
 def __init__(self,a,b=None): self.a=a;self.b=a if b is None else b
 @staticmethod
 def rat(a,b=1):return I(floorq(a*S,b),ceilq(a*S,b))
 def __add__(x,y):
  if isinstance(y,int):y=I.rat(y)
  return I(x.a+y.a,x.b+y.b)
 __radd__=__add__
 def __neg__(x):return I(-x.b,-x.a)
 def __sub__(x,y):return x+-y
 def __mul__(x,y):
  if isinstance(y,int):y=I.rat(y)
  c=[x.a*y.a,x.a*y.b,x.b*y.a,x.b*y.b]
  return I(floorq(min(c),S),ceilq(max(c),S))
 __rmul__=__mul__
 def __truediv__(x,y):
  if isinstance(y,int):y=I.rat(y)
  assert y.a>0
  return x*I(floorq(S*S,y.b),ceilq(S*S,y.a))
 def sq(x):
  return I(0 if x.a<=0<=x.b else floorq(min(x.a*x.a,x.b*x.b),S),ceilq(max(x.a*x.a,x.b*x.b),S))
 def wide(x,digits=12):
  T=10**digits
  return {'lower_numerator':floorq(x.a*T,S),'upper_numerator':ceilq(x.b*T,S),'denominator':T}
 def exact(x):return {'a':str(x.a),'b':str(x.b),'scale':str(S)}
def atan_interval(d,n=159):
 assert n%2==1
 a=sum((Fraction((-1)**j,(2*j+1)*d**(2*j+1)) for j in range(n+1)),Fraction(0))
 e=Fraction(1,(2*n+3)*d**(2*n+3))
 return I(floorq(a.numerator*S,a.denominator),ceilq((a+e).numerator*S,(a+e).denominator))
pi=16*atan_interval(5)-4*atan_interval(239)
assert pi.a>I.rat(314159265358979,10**14).b
assert pi.b<I.rat(314159265358980,10**14).a
M=240;K=32
def entire_series(z,ball=False):
 term=I.rat(1,3) if ball else I.rat(1)
 val=term
 for j in range(M):
  # this creates term number j+1
  term=term*z*(j+2)/((j+1)*(2*j+4)*(2*j+5)) if ball else term*z/((j+1)*(j+2))
  val=val+((-term) if (j+1)%2 else term)
 nxt=term*z*(M+2)/((M+1)*(2*M+4)*(2*M+5)) if ball else term*z/((M+1)*(M+2))
 # decreasing alternating remainder: ratios decrease thereafter and are below 1
 ratio=z*(M+2)/((M+1)*(2*M+4)*(2*M+5)) if ball else z/((M+1)*(M+2))
 assert ratio.b<S and nxt.b<10**120
 return I(val.a-nxt.b,val.b+nxt.b)
counts2=Counter(x*x+y*y for x in range(-K,K+1) for y in range(-K,K+1) if 0<x*x+y*y<=K*K)
counts3=Counter(x*x+y*y+z*z for x in range(-K,K+1) for y in range(-K,K+1) for z in range(-K,K+1) if 0<x*x+y*y+z*z<=K*K)
def energy(v,kind):
 counts=counts3 if kind=='B1' else counts2
 mass=I.rat(0);energy=I.rat(0)
 for q,c in sorted(counts.items()):
  if kind=='B1':a=3*v*entire_series(4*pi.sq()*q/9,True)
  elif kind=='T1':a=v*entire_series(4*pi.sq()*q/81)
  else:a=v*entire_series(I.rat(q))
  a2=a.sq();mass=mass+c*a2;energy=energy+c*a2/(4*pi.sq()*q)
 residual=v-v.sq()-mass
 assert residual.a>0
 tail=residual/(4*pi.sq()*(K*K+1))
 return I(energy.a,energy.b+tail.b),{'finite_energy':energy.exact(),'finite_mass':mass.exact(),'residual':residual.exact(),'tail_upper':str(tail.b),'distinct_q':len(counts),'modes':sum(counts.values())}
v1=4*pi/81;v2=I.rat(1)/pi
B1,binfo=energy(v1,'B1');T1,t1info=energy(v1,'T1');T2,t2info=energy(v2,'T2')
S2=v2.sq()*(I.rat(1)-v2).sq()/12
d1=T1-B1;d2=T2-S2
assert d1.a>0 and d2.a>0
shift1=2*d1/3;shift2=-d2/pi
out={'method':'integer outward intervals, Machin/alternating series, finite Fourier modes, Parseval residual tail','K':K,'series_degree':M,'precision_decimal_places':180,'pi':pi.exact(),'energies':{k:x.wide() for k,x in [('B1',B1),('T1',T1),('T2',T2),('S2',S2)]},'gaps':{'T1-B1':d1.wide(),'T2-S2':d2.wide()},'first_order_crossing_shifts':{'ball_tube':shift1.wide(),'tube_slab':shift2.wide()},'exact':{k:x.exact() for k,x in [('B1',B1),('T1',T1),('T2',T2),('S2',S2),('gap1',d1),('gap2',d2),('shift1',shift1),('shift2',shift2)]},'finite_certificates':{'B1':binfo,'T1':t1info,'T2':t2info}}
root=Path(__file__).resolve().parent
if '--stdout-only' not in sys.argv:
 (root/'private/nonlocal-rational-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['pi','exact','finite_certificates']},indent=2))
