from research import V,mu
from pathlib import Path
from math import gcd
import itertools,collections,json
L=Path(__file__).parent
for m in range(1,201):
 n=6*m+2;a=3
 pts=[((a*k+n-1)//n,k) for k in range(1,n)]
 assert sum(x%2==k%2==0 for x,k in pts)==m
 assert V(a,n)==3*m+1+(4*m+1)//3
 n=8*m;a=4*m-1
 assert gcd(a,n)==1 and pow(a,-1,n)==a
for n in range(4,91):
 for a in range(2,n-1):
  if gcd(a,n)>1:continue
  pts=[((a*k+n-1)//n,k) for k in range(1,n)]
  As=[n-1]+[sum((s*n)//a-((d*s-1)*n)//(a*d) for s in range(1,a//d+1)) for d in range(2,a+1)]
  assert sum(mu(d)*As[d-1] for d in range(1,a+1))==V(a,n)
  rays={}
  for x,k in pts:
   g=gcd(x,k);p=(x//g,k//g);rays[p]=rays.get(p,0)+1
  assert all(c==(n-1)//max(k,n*x-a*k) for (x,k),c in rays.items())
for a,n,p in [(5,14,(2,4))]:
 q=(a+1-p[0],n-p[1]);assert q==(4,10) and gcd(*p)>1 and gcd(*q)>1
assert gcd(3,6)>1 and gcd(4,6)>1 # a=5,n=13 complementary slopes at k=6
for n in range(4,65):
 for a in range(2,n-1):
  if gcd(a,n)>1:continue
  printed=sum(sum(gcd(s,k)==1 for k in range((s-1)*n//a+1,s*n//a+1)) for s in range(1,a+1))
  assert printed==V(a,n)+1
assert V(2,5)==3
grid=[]
for r in [2,3]:
 vs=list(itertools.product(range(3),repeat=r));E=[(x,y) for x in vs for y in vs if x<y and sum(abs(i-j) for i,j in zip(x,y))==1]
 def dist(x,y):return sum(abs(i-j) for i,j in zip(x,y))
 for x,y in E:assert sorted([sum(dist(z,x)<dist(z,y) for z in vs),sum(dist(z,y)<dist(z,x) for z in vs)])==[3**(r-1),2*3**(r-1)]
 grid.append(dict(r=r,vertices=len(vs),edges=len(E),degrees=sorted(set(sum(x in e for e in E) for x in vs)),transmissions=sorted(set(sum(dist(x,y) for y in vs) for x in vs))))
(L/'mechanism-checks.json').write_text(json.dumps({'status':'PASS','grid':grid,'floor_identity_bound':90,'infinite_family_diagnostics_m':200,'note':'Finite diagnostics only; universal arguments in discovery.md'},indent=2))
print('Mechanism and independent grid checks PASS')
