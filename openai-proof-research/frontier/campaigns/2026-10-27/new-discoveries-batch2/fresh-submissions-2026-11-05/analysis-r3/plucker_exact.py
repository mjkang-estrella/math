from fractions import Fraction as F
from functools import lru_cache
from math import comb
from pathlib import Path
import json,time
# Homogeneous polynomials represented by coefficient of a^j b^(degree-j).
def mul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def twist(a,q):
 L=len(a)-1;c=[F(0)]*(L+1)
 for j,v in enumerate(a):
  for k in range(L-j+1):c[j+k]+=v*(1+q)**j*comb(L-j,k)*q**k
 return c
def step(a,d,m,e):
 if len(a)>1:a=twist(a,F(m,d-m))
 for k in range(m):a=mul(a,[F(d-k),F(k)])
 L=len(a)-1;anti=[a[j]-a[L-j] for j in range(L+1)];g=[];s=0
 for j in range(L):s+=anti[j];g.append(s/e)
 assert s+anti[L]==0 and g==g[::-1]
 return tuple(g)
@lru_cache(None)
def cls(lam,d):
 if not lam:return (F(1),)
 m=lam[-1];return step(cls(lam[:-1],d-m),d,m,lam.count(m))
def parts(n,lo=2):
 if n==0:yield ()
 for j in range(lo,n+1):
  for rest in parts(n-j,j):yield (j,)+rest
def diffs(v):
 ans=[]
 while v:
  ans.append(v[0]);v=[b-a for a,b in zip(v,v[1:])]
 return ans
def data(lam):
 N=sum(lam);M=N-len(lam);vs=[cls(lam,N+x) for x in range(N+2)];out=[]
 for i in range((M+1)//2,M+1):
  j=M-i;v=[g[j]-(g[j-1] if j else 0) for g in vs];cs=diffs(v)
  assert cs[-1]==0 # extra-degree validation, not a proof of global degree
  cs=cs[:-1]
  out.append((i,cs))
 return out
start=time.time();rows=[];bad=[];total=0
for N in range(2,13):
 for lam in parts(N):
  for i,c in data(lam):
   total+=1
   fail=[j for j,z in enumerate(c) if z<0 or (0<j<len(c)-1 and z*z<c[j-1]*c[j+1])]
   if fail:bad.append({'partition':lam,'i':i,'coefficients':list(map(str,c)),'fail':fail})
  rows.append(lam)
# Exact source examples independently reconstruct.
examples={str(lam):{str(i):list(map(str,c)) for i,c in data(lam)} for lam in [(2,2),(2,2,2),(3,3)]}
assert examples['(2, 2)']['1']==list(map(str,[28,92,112,60,12]))
assert examples['(2, 2, 2)']['2']==list(map(str,[624,3184,6768,7680,4912,1680,240]))
assert examples['(3, 3)']['3']==list(map(str,[2412,10566,19368,19026,10512,3060,360]))
result={'N_max':12,'partitions':len(rows),'coefficient_rows':total,'failures':bad,'examples':examples,'seconds':time.time()-start,'arithmetic':'fractions.Fraction; Theorem2.7 recurrence; no floating point','scope':'bounded diagnostic only; no all-partition proof'}
Path(__file__).with_name('plucker-exact.json').write_text(json.dumps(result,indent=2));print({k:v for k,v in result.items() if k!='examples'})
