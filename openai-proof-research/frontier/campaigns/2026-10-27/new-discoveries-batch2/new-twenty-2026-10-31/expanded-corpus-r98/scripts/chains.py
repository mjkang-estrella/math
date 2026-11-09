import functools,itertools,json,sys
from fractions import Fraction as F
from collections import defaultdict
from pathlib import Path
D=Path(__file__).resolve().parents[1]
@functools.lru_cache(None)
def parts(n,lo=1):
 if not n:return ((),)
 return tuple((s,)+p for s in range(lo,n+1) for p in parts(n-s,s))
def types(r):return ((nu,p) for nu in range(r+1) for p in parts(r-nu))
def deg(t):return t[0]+sum(t[1])-len(t[1])
def edges(t):
 nu,p=t;a=[(i,i) for i in range(nu)];o=nu
 for s in p:a += [(o+i,o+i+1) for i in range(s-1)];o+=s
 return a

def typ(r,es):
 par=list(range(r));nu=0
 def root(x):
  while par[x]!=x:x=par[x]
  return x
 loops=set()
 for a,b in es:
  if a==b:nu+=1;loops.add(a)
  else:par[root(a)]=root(b)
 c=defaultdict(int)
 for i in range(r):
  if i not in loops:c[root(i)]+=1
 return nu,tuple(sorted(c.values()))
@functools.lru_cache(None)
def zeta(t,w):
 es=edges(t);r=t[0]+sum(t[1]);s=deg(w)
 return sum(typ(r,a)==w for a in itertools.combinations(es,s))
def add(P,i,j,c):
 if c:P[i,j]+=c
@functools.lru_cache(None)
def poly(t):
 nu,mu=t;r=nu+sum(mu);d=deg(t)
 if r==d:return {(0,0):F(1)}
 P=defaultdict(F)
 if 1 in mu:
  v=list(mu);v.remove(1);old=poly((nu,tuple(v)));m=mu.count(1);l=r-d-1;g=nu+1
  for (a,b),c in old.items():
   for i,j,coef in [(1,1,l),(1,0,3*l+g),(0,1,r+2*l),(0,0,4*l+2*g)]:add(P,a+i,b+j,c*coef/m)
   for i,j,coef in [(2,1,1),(2,0,2),(1,1,1),(1,0,2)]:
    if a:add(P,a-1+i,b+j,-c*a*coef/m)
   for i,j,coef in [(1,2,1),(0,2,2),(1,1,1),(0,1,2)]:
    if b:add(P,a+i,b-1+j,-c*b*coef/m)
 else:
  w=(nu,tuple(x-1 for x in mu if x>1));s=deg(w)
  for tp in types(d):
   sp=deg(tp);np=tp[0]
   if not(s<=sp and nu<=np and sp-np>=s-nu):continue
   z=zeta(tp,w)
   if not z:continue
   for (a,b),c in poly(tp).items():
    # (zw+z+w)^a w^b, times prefactor
    for i in range(a+1):
     for j in range(a-i+1):
      k=a-i-j
      import math
      coef=math.comb(a,i)*math.comb(a-i,j)
      for h in range(np-nu+1):add(P,sp-s+i+j,sp-np-s+nu+b+i+k+h,c*z*(-1)**(sp-s)*coef*math.comb(np-nu,h))
 P={k:c for k,c in P.items() if c};assert all(c.denominator==1 for c in P.values()),t
 assert max(sum(k) for k in P)==r-d,(t,P)
 return P
res=[]
for r in range(int(sys.argv[1])+1):
 ts=list(types(r));bad=[]
 for t in ts:
  p=poly(t)
  if min(p.values())<0:bad.append({'type':t,'polynomial':[[a,b,str(c)] for (a,b),c in sorted(p.items())]})
 row=dict(r=r,types=len(ts),negative=bad);res.append(row);print(json.dumps(row),flush=True)
 if bad:break
(D/'outputs/chains.json').write_text(json.dumps(res,indent=2)+'\n')
