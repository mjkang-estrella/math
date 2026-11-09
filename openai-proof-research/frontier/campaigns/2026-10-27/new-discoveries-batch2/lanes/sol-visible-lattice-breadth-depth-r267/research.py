from pathlib import Path
from math import gcd
import json,time,urllib.request,urllib.parse,hashlib
L=Path(__file__).resolve().parent
def V(a,n):return sum(gcd((a*k+n-1)//n,k)==1 for k in range(1,n))
def mu(d):
 s=1;p=2
 while p*p<=d:
  if d%p==0:
   d//=p;s=-s
   if d%p==0:return 0
   while d%p==0:d//=p
  p+=1
 return -s if d>1 else s
out={'bound':350,'pairs':0,'conjecture_violations':[],'parity_upper_failure':None,'reflection_failure':None,'same_ray_failure':None,'inverse_central_failure':None}
for n in range(4,351):
 for a in range(2,n-1):
  if gcd(a,n)>1:continue
  pts=[((a*k+n-1)//n,k) for k in range(1,n)]
  v=sum(gcd(x,k)==1 for x,k in pts);out['pairs']+=1
  assert v==V(pow(a,-1,n),n)
  if not (2*v>n and 4*v<3*n):out['conjecture_violations'].append([a,n,v])
  even=sum(x%2==k%2==0 for x,k in pts)
  if even<=n/4-1 and out['parity_upper_failure'] is None:out['parity_upper_failure']=[a,n,v,even]
  bad=[(x,k) for x,k in pts if gcd(x,k)>1]
  if out['reflection_failure'] is None:
   for x,k in bad:
    if gcd(a+1-x,n-k)>1:out['reflection_failure']=[a,n,[x,k],[a+1-x,n-k]];break
  if out['same_ray_failure'] is None:
   rays={}
   for x,k in bad:
    g=gcd(x,k);p=(x//g,k//g);rays.setdefault(p,[]).append((x,k))
   for p,ps in rays.items():
    if len(ps)>1:out['same_ray_failure']=[a,n,p,ps];break
  if n<=75:
   # Independent column formula with strictly interior endpoints.
   col=sum(sum(gcd(s,k)==1 for k in range((s-1)*n//a+1,min(n-1,(s*n-1)//a)+1)) for s in range(1,a+1))
   assert col==v
   As=[]
   for d in range(1,a+1):
    direct=sum(x%d==k%d==0 for x,k in pts)
    residue=sum(0<((-a*t)%n)*d<n for t in range(1,(n-1)//d+1))
    assert direct==residue;As.append(direct)
   assert sum(mu(d)*As[d-1] for d in range(1,a+1))==v
(L/'exact-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out))
