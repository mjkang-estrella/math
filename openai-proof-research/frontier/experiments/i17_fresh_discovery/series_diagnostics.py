"""Supplementary exact jets of the rational certificate; not a sufficiency proof."""
from fractions import Fraction as Q
from pathlib import Path
import json,random
import sys
sys.dont_write_bytecode=True
import diagnostics as d
ORDER=8
class S:
 def __init__(self,x=0):
  if isinstance(x,S):self.c=x.c[:]
  elif isinstance(x,(list,tuple)):self.c=list(map(Q,x[:ORDER+1]))+[Q(0)]*max(0,ORDER+1-len(x))
  else:self.c=[Q(x)]+[Q(0)]*ORDER
 def __add__(self,x):
  x=S(x);return S([a+b for a,b in zip(self.c,x.c)])
 __radd__=__add__
 def __neg__(self):return S([-a for a in self.c])
 def __sub__(self,x):return self+-S(x)
 def __rsub__(self,x):return S(x)+-self
 def __mul__(self,x):
  x=S(x);return S([sum(self.c[j]*x.c[k-j] for j in range(k+1)) for k in range(ORDER+1)])
 __rmul__=__mul__
 def inv(self):
  assert self.c[0]
  out=[1/self.c[0]]
  for k in range(1,ORDER+1):out.append(-sum(self.c[j]*out[k-j] for j in range(1,k+1))/self.c[0])
  return S(out)
 def __truediv__(self,x):return self*S(x).inv()
 def __rtruediv__(self,x):return S(x)*self.inv()
 def __pow__(self,k):
  assert k>=0;r=S(1)
  for _ in range(k):r=r*self
  return r
 def __bool__(self):return any(self.c)
 def __eq__(self,x):return self.c==S(x).c
 def __str__(self):return str(self.c)
def solve(M,b):
 n=len(M);a=[[S(x) for x in row]+[S(v)] for row,v in zip(M,b)]
 for j in range(n):
  p=next(i for i in range(j,n) if a[i][j].c[0]);a[j],a[p]=a[p],a[j]
  z=a[j][j];a[j]=[x/z for x in a[j]]
  for i in range(n):
   if i!=j:
    z=a[i][j];a[i]=[x-z*y for x,y in zip(a[i],a[j])]
 return [a[i][-1] for i in range(n)]
d.solve=solve

def run(T,velocity):
 U=[S([t,w]) for t,w in zip(T,velocity)];V=d.mobius(T,U)
 assert V[:3]==U[:3]
 prev=V[:];rp=d.residuals(T,prev);assert all(x==0 for x in rp)
 columns=[]
 for k in range(3,6):
  curr=prev[:];curr[k]=U[k];rc=d.residuals(T,curr);v=U[k]-V[k]
  assert v.c[0]==0 and v.c[1]!=0
  # Divide by epsilon first; coefficient ORDER is discarded as unknown.
  cols=[]
  for x,y in zip(rc,rp):
   numerator=x-y;assert numerator.c[0]==0
   cols.append(S(numerator.c[1:])/S(v.c[1:]))
  columns.append(cols);prev=curr;rp=rc
 A=[[columns[k][j] for k in range(3)] for j in range(3)]
 b=[columns[k][3] for k in range(3)];c=solve(list(map(list,zip(*A))),b)
 assert all(x.c[0]==0 for x in c)
 pv=[d.J(t,u)-d.dot(c,d.a(t,u)) for t,u in zip(T,U)]
 coeff=solve([d.h(t,u) for t,u in zip(T[:5],U[:5])],pv[:5]);assert all(x.c[0]==0 for x in coeff)
 errors=[d.J(t,u)-d.dot(c,d.a(t,u))-d.dot(coeff,d.h(t,u)) for t,u in zip(T,U)]
 assert all(all(z==0 for z in e.c[:ORDER]) for e in errors)
 # Independent verification of A's constant coefficient formula.
 prime=[d.product_value(t-s for s in T if s!=t) for t in T]
 mus=[prime[-1]/p for p in prime]
 expected=[[mus[k]*f(T[k]) for k in range(3,6)] for f in (lambda t:Q(1),lambda t:2*t,lambda t:t*t)]
 assert [[x.c[0] for x in row] for row in A]==expected
 return {'T':list(map(str,T)),'velocity':list(map(str,velocity)),'c_constant':[str(x.c[0]) for x in c],'d_constant':[str(x.c[0]) for x in coeff],'checked_through_order':ORDER-1}
if __name__=='__main__':
 rng=random.Random(172027);runs=[]
 for i in range(12):
  T=list(map(Q,rng.sample(range(-12,13),6)));v=list(map(Q,rng.sample(range(-30,31),6)))
  runs.append(run(T,v))
 out={'status':'PASS','runs':runs,'equations_checked':6*len(runs),'scope':'Exact order-7 checks of rational formulas; report supplies exact all-order/local-ring proof.'}
 Path(__file__).with_name('series-diagnostics.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS:',len(runs),'series directions,',len(runs)*6,'equations through order',ORDER-1)
