"""Exact rational, outward rounded interval certificate; no floating arithmetic."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json
L=Path(__file__).resolve().parent;S=10**32
def floor(x):return x.numerator//x.denominator
def ceil(x):return -floor(-x)
class I:
 def __init__(self,a,b=None):self.a=F(floor(F(a)*S),S);self.b=F(ceil(F(a if b is None else b)*S),S)
 def __add__(x,y):
  if not isinstance(y,I):y=I(y)
  return I(x.a+y.a,x.b+y.b)
 __radd__=__add__
 def __neg__(x):return I(-x.b,-x.a)
 def __sub__(x,y):return x+-toI(y)
 def __rsub__(x,y):return toI(y)+-x
 def __mul__(x,y):
  y=toI(y);v=[x.a*y.a,x.a*y.b,x.b*y.a,x.b*y.b];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(x,y):
  y=toI(y);assert y.a*y.b>0;return x*I(1/y.b,1/y.a)
def toI(x):return x if isinstance(x,I) else I(x)
def exp_pos(x):
 assert 0<=x<=8
 term=I(1);out=term
 for k in range(1,121):term=term*x/k;out=out+term
 return out+I(0,F(2*8**121,factorial(121)))
def log_reduced(y):
 assert y.a>=1 and y.b<=2
 z=(y-1)/(y+1);z2=z*z;term=z;out=I(0)
 for k in range(100):out=out+term/F(2*k+1);term=term*z2
 return 2*out+I(0,F(1,3**199))
log2=log_reduced(I(2))
def log_endpoint(x):
 k=0
 while x<1:x*=2;k-=1
 while x>2:x/=2;k+=1
 return log_reduced(I(x))+k*log2
def log_interval(x):return I(log_endpoint(x.a).a,log_endpoint(x.b).b)
rows=json.loads((L/'check-results.json').read_text());r=next(x for x in rows if x['theta']==8 and x['m']==20 and x['a']==.5)
ts=[F(str(x)) for x in r['thresholds']]
e={u:I(1)/exp_pos(8*u) for u in ts};q=I(1)/exp_pos(F(8))
cov=I(0);var=F(0)
for u in ts:
 for v in ts:
  C=-log_interval(1-(1-e[u])*(1-e[v])/(1-q))/8
  cov=cov+C-u*v;var+=min(u,v)-u*v
ordinal=cov/var
# Integral J_j = integral_0^8 t^j/(exp(t)-1) dt.
# Bernoulli expansion on [0,8] is unsuitable; integrate positive exp series.
# The omitted k>K tail of J_j is <= j!/(j*K^j).
K=20000;J1=I(0);J2=I(0);qk=q
for k in range(1,K+1):
 J1=J1+(1-(1+8*k)*qk)/F(k*k)
 J2=J2+(2-(2+16*k+64*k*k)*qk)/F(k**3)
 qk=qk*q
J1=J1+I(0,F(1,K));J2=J2+I(0,F(1,K*K))
rho=1-F(12,64)*J1+F(24,512)*J2
assert ordinal.a>F(804,1000) and rho.b<F(804,1000)
def pair(x):return [str(x.a),str(x.b)]
out=dict(theta=8,categories=20,thresholds=[str(t) for t in ts],ordinal=pair(ordinal),latent=pair(rho),separating_rational='201/250',strict_verified=True,K=K,arithmetic='exact Fraction endpoints, outward quantization to 10^-32',precision_is_not_proof='All series tails enclosed analytically; assertions use rational comparisons')
(L/'certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
