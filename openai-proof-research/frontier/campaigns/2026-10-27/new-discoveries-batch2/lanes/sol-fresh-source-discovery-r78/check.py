from fractions import Fraction as F
from math import factorial as fac,gcd
from collections import Counter,defaultdict
import json
# Sparse polynomials in b,c only.
def add(a,b):
 d=defaultdict(F,a)
 for k,v in b.items(): d[k]+=v
 return {k:v for k,v in d.items() if v}
def mul(a,b):
 d=defaultdict(F)
 for (i,j),v in a.items():
  for (k,l),w in b.items(): d[i+k,j+l]+=v*w
 return {k:v for k,v in d.items() if v}
def scale(a,s):return {k:v*s for k,v in a.items() if v*s}
def binom_poly(n,axis):
 a={(0,0):F(1)}
 for r in range(n):a=mul(a,{(1,0) if axis==0 else (0,1):F(1),(0,0):F(-r)})
 return scale(a,F(1,fac(n)))
def comp(n,k):
 if k==1:yield(n,);return
 for i in range(n+1):
  for tail in comp(n-i,k-1):yield(i,)+tail
# Maximal NE path below the diagonal of the 4 by 5 rectangle.
path=[];y=0
for x in range(1,5):
 path.append('E')
 while y<(5*x)//4:path.append('N');y+=1
H=[i for i,e in enumerate(path) if e=='E'];V=[i for i,e in enumerate(path) if e=='N'];L=len(path)
def segment(u,v):
 out=[u]
 while out[-1]!=v:out.append((out[-1]+1)%L)
 return out
def compatible(w):
 for u in H:
  if not w[u]:continue
  for v in V:
   if not w[v]:continue
   s=segment(u,v);ok=False
   for t,e in enumerate(s):
    if path[e]=='N' and e!=v:
     if sum(path[z]=='N' for z in s[:t+1])==sum(w[z] for z in s[:t+1] if path[z]=='E'):ok=True;break
    if path[e]=='E' and e!=u:
     if sum(path[z]=='E' for z in s[t:])==sum(w[z] for z in s[t:] if path[z]=='N'):ok=True;break
   if not ok:return False
 return True
def shadow_h(u,w):
 s=[]
 for t in range(L):
  e=(u+t)%L;s.append(e)
  if path[e]=='N' and sum(path[z]=='N' for z in s)==sum(w[z] for z in s if path[z]=='E'):
   return {z for z in s if path[z]=='N'}
 return set(V)
lam=Counter();examined=0
for wh in comp(4,len(H)):
 for wv in comp(3,len(V)):
  examined+=1;w=[0]*L
  for e,z in zip(H,wh):w[e]=z
  for e,z in zip(V,wv):w[e]=z
  if not compatible(w):continue
  sh=set().union(*(shadow_h(u,w) for u in H if w[u]))
  if not all(v in sh for v in V if w[v]):continue
  lam[tuple(sorted((z for z in wv if z),reverse=True)),tuple(sorted((z for z in wh if z),reverse=True))]+=1
rho={}
for (p,q),n in lam.items():
 t={(0,0):F(n)}
 for z in p:t=mul(t,binom_poly(z,1))
 for z in q:t=mul(t,binom_poly(z,0))
 rho=add(rho,t)
assert all(i>=1 and j>=1 for i,j in rho)
A={(i-1,j-1):v for (i,j),v in rho.items()}
bm={(1,0):F(1),(0,0):F(-1)}
cm={(0,1):F(4),(0,0):F(-3)}
u=mul(bm,cm)
expected=scale(mul(mul(bm,add(u,{(0,0):F(-1)})),add(u,{(0,0):F(-2)})),F(1,24))
assert A==expected,(A,expected)
assert lam[((3,),(4,))]==1
assert all((24*v).denominator==1 for v in A.values())
# All unordered block-counts in the divided-power transport lemma.
def counts(k,s=1):
 if s>k:yield {};return
 for a in range(k//s+1):
  for tail in counts(k-a*s,s+1) if k-a*s else [{}]:
   yield dict(tail,**{})|({s:a} if a else {})
# Use standard integer partitions, avoiding a recursion with moving remainder bound.
def parts(k,lo=1):
 if k==0:yield();return
 for s in range(lo,k+1):
  for tail in parts(k-s,s):yield(s,)+tail
block_tests=0
for m in range(1,7):
 for k in range(1,13):
  for p in parts(k):
   den=1
   for s,a in Counter(p).items():den*=fac(a)*fac(m*s)**a
   assert fac(m*k)%den==0
   block_tests+=1
obstruction=F(24*fac(6),fac(5)**2)
assert obstruction==F(6,5)
assert F(fac(5),fac(4)*fac(3))==F(5,6)
result={'status':'diagnostic only, no full C4 proof','path':''.join(path),'gradings_examined':examined,'tight_gradings':sum(lam.values()),'lambda':[{ 'P1':p,'P2':q,'count':n} for (p,q),n in sorted(lam.items())],'A34_terms':{str(k):str(v) for k,v in sorted(A.items())},'singleton_scaled_top_coefficient':str(F(24,fac(3)*fac(4))),'aggregate_scaled_top_coefficient':str(24*A[3,2]),'block_partition_checks':block_tests,'poisson_lattice_obstruction':str(obstruction),'integer_valued_shortcut_obstruction':'5/6'}
print(json.dumps(result,indent=2))
