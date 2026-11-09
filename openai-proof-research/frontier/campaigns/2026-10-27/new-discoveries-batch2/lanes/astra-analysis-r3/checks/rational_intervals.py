"""Exact rational enclosures. No floating point used for certification.

For 1<=x<=2, t=(x-1)/(x+1) in [0,1/3], and
0 <= log(x)-2*sum_{j=0}^{N-1} t^(2j+1)/(2j+1)
  <= 2*t^(2*N+1)/((2*N+1)*(1-t*t)).
Scale by powers of 2, enclosing log 2 by the same series.
All interval operations round OUTWARD to rational multiples of 10^-80.
"""
from fractions import Fraction as F
from pathlib import Path
import json
S=10**80

def down(x):return F((x*S).numerator//(x*S).denominator,S)
def up(x):return -down(-x)
class I:
 def __init__(self,a,b=None):self.a=down(F(a));self.b=up(F(a if b is None else b));assert self.a<=self.b
 def __add__(self,o):
  o=cv(o);return I(self.a+o.a,self.b+o.b)
 __radd__=__add__
 def __neg__(self):return I(-self.b,-self.a)
 def __sub__(self,o):return self+-cv(o)
 def __rsub__(self,o):return cv(o)+-self
 def __mul__(self,o):
  o=cv(o);v=[a*b for a in [self.a,self.b] for b in [o.a,o.b]];return I(min(v),max(v))
 __rmul__=__mul__
 def inv(self):assert self.a*self.b>0;return I(1/self.b,1/self.a)
 def __truediv__(self,o):return self*cv(o).inv()
 def __rtruediv__(self,o):return cv(o)*self.inv()
 def __pow__(self,n):
  assert isinstance(n,int) and n>=0
  r=I(1)
  for _ in range(n):r=r*self
  return r
 def out(self):return {'lower':str(self.a),'upper':str(self.b),'strict_positive':self.a>0,'strict_negative':self.b<0}
def cv(x):return x if isinstance(x,I) else I(x)
def unitlog(x,N=100):
 assert 1<=x<=2
 t=(x-1)/(x+1);t2=t*t;v=t;s=F(0)
 for j in range(N):s+=2*v/(2*j+1);v*=t2
 return I(s,s+2*v/((2*N+1)*(1-t2)))
LOG2=unitlog(F(2))
def rational_log(x):
 x=F(x);assert x>0;e=0
 while x<1:x*=2;e-=1
 while x>2:x/=2;e+=1
 return unitlog(x)+e*LOG2
def log(x):
 x=cv(x);assert x.a>0
 return I(rational_log(x.a).a,rational_log(x.b).b)
def L(a,b):return (b-a)/(log(b)-log(a))
def D(a,b,c):
 assert a.b<b.a and b.b<c.a
 return (((log(b)-log(a))/(b-a)-(log(c)-log(b))/(c-b))/(c-a),
  ((c*log(c)-b*log(b))/(c-b)-(b*log(b)-a*log(a))/(b-a))/(c-a))
def certify(v):
 a,b,c=map(I,v);x,y,z=L(a,b),L(a,c),L(b,c)
 old0,old1=D(a,b,c);new0,new1=D(x,y,z)
 assert old0.a>0 and old1.a>0 and new0.a>0 and new1.a>0
 residual0=old0-new0;residual1=new1-old1
 assert residual0.a>0 and residual1.a>0
 # Positive means shortcut fails: U0>G(T), respectively A(T)>U1.
 gfail=1-(2*old0)**3*(x*y*z)**2
 afail=2*old1*(x+y+z)-3
 return {'triple':v,'D0(v)-D0(Tv)':residual0.out(),'D1(Tv)-D1(v)':residual1.out(),
  '1-(2D0)^3*(xyz)^2':gfail.out(),'2D1*(x+y+z)-3':afail.out()}
if __name__=='__main__':
 triples=[(1,2,3),(1,10,11),(10,11,100),(1,2,100),(1,99,100),(1,10**6,10**12),(1000,1001,1002)]
 out={'method':'100-term exact atanh log series, power-of-two reduction; 80-decimal outward rational rounding',
  'scope':'Seven individual strict Conjecture16 checks only; no full theorem, no Lean certificate',
  'checks':[certify(v) for v in triples]}
 Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2))
 for r in out['checks']:print(r['triple'],'both target signs certified; G1 shortcut fails:',r['1-(2D0)^3*(xyz)^2']['strict_positive'],'A1 shortcut fails:',r['2D1*(x+y+z)-3']['strict_positive'])
