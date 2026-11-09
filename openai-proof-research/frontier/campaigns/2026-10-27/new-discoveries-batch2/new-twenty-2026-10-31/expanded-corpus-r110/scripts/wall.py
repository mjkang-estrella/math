from functools import lru_cache
from collections import Counter
from fractions import Fraction
import json,random

def transpose(p):return tuple(sum(v>j for v in p) for j in range(p[0] if p else 0))
def removable(p):return [(i,v-1) for i,v in enumerate(p) if i==len(p)-1 or v>p[i+1]]
def addable(p):return [(i,v) for i,v in enumerate(p) if i==0 or v<p[i-1]]+[(len(p),0)]
def remove(p,c):
 a=list(p);a[c[0]]-=1;return tuple(v for v in a if v)
def add(p,c):
 a=list(p)+([0] if c[0]==len(p) else []);a[c[0]]+=1;return tuple(a)
def good(p,d):
 out=[]
 for r in range(d):
  items=[(c,'R') for c in removable(p) if (c[1]-c[0])%d==r]+[(c,'A') for c in addable(p) if (c[1]-c[0])%d==r];items.sort(key=lambda x:(-x[0][0],x[0][1]));s=[]
  for c,t in items:
   if t=='A' and s and s[-1][1]=='R':s.pop()
   else:s.append((c,t))
  for c,t in s:
   if t=='R':out.append((c,r));break
 return out
@lru_cache(None)
def M(p,d):
 if not p:return ()
 ct=Counter(p);nu=tuple(sorted([v for v,m in ct.items() for _ in range(m%d)],reverse=True));rho=tuple(sorted([v for v,m in ct.items() for _ in range(m//d)],reverse=True))
 if rho:return tuple(sorted(M(nu,d)+tuple(v for v in transpose(rho) for _ in range(d)),reverse=True))
 c,r=good(p,d)[0];q=M(remove(p,c),d);opts=[]
 for c2 in addable(q):
  z=add(q,c2)
  if (c2[1]-c2[0])%d==(-r)%d and any(c2==x for x,r2 in good(z,d)):opts.append(z)
 assert len(opts)==1,(p,d,q,opts)
 return opts[0]
def parts(n,hi=None):
 if not n:yield ();return
 for a in range(min(n,hi or n),1-1,-1):
  for p in parts(n-a,a):yield (a,)+p
rng=random.Random(110)
for n in list(range(1,13))+[41,42,48]:
 ps=list(parts(n)) if n<=12 else [tuple(sorted([rng.randrange(1,10) for _ in range(5)],reverse=True)) for i in range(30)]
 if n>12:
  # Make random partitions of exactly n by random cuts.
  ps=[]
  for _ in range(50):
   cuts=sorted(rng.sample(range(1,n),rng.randrange(1,8)));ps.append(tuple(sorted([b-a for a,b in zip([0]+cuts,cuts+[n])],reverse=True)))
 checked=fail=0;involution=0;example=None
 walls=sorted({Fraction(a,b) for b in range(2,n+2) for a in range(1,b)})
 for p in ps:
  q=(p[0]+1,)+p[1:];x=p;y=q
  for f in walls:
   b=f.denominator
   z=M(x,b);assert M(z,b)==x;involution+=1
   x=transpose(z);y=transpose(M(y,b));checked+=1
   # Only nesting tested: good-box convention after transposition needs separate audit.
   X={(i,j) for i,v in enumerate(x) for j in range(v)};Y={(i,j) for i,v in enumerate(y) for j in range(v)}
   if not X<Y:
    fail+=1
    if example is None:example=dict(partition=p,wall=str(f),x=x,y=y)
 print(json.dumps(dict(n=n,initial_partitions=len(ps),wall_steps=checked,nesting_failures=fail,example=example,involution_checks=involution,scope='Mullineux implementation diagnostic; nesting only; good-box endpoint unverified')),flush=True)
