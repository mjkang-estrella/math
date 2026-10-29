"""Independent diagnostics: row interval floors and actual quotient graph BFS, no rotated square."""
from collections import deque,Counter
from math import gcd
import pathlib,json
D=pathlib.Path(__file__).resolve().parent
primes=[p for p in range(3,102) if all(p%d for d in range(2,int(p**.5)+1))]
rows=[];branches=Counter()
for s in range(0,121):
 for p in primes:
  hist=[[0]*p for _ in range(p)]
  for x in range(-s,s+1):
   h=s-abs(x)
   for j in range(p): hist[x%p][j]+=(h-j)//p-((-h-1-j)//p)
  actual=min(map(min,hist));q,r=divmod(2*s+1,p)
  branch='even-q' if q%2==0 else ('odd-many-short' if r<p-1 else 'odd-one-short')
  expected=q*q//2 if q%2==0 else (q*q+(-1 if r<p-1 else 1))//2
  assert actual==expected,(s,p,actual,expected)
  if s>=3 and r: assert p*p*actual<=2*s*s,(s,p)
  branches[branch]+=1;rows.append([s,p,q,r,actual])
# BFS in the HNF quotient Z^2/<(a,0),(b,d)>; graph distance, not diamond-image enumeration.
def diameter(a,b,d,limit):
 def norm(x,y):
  t,y=divmod(y,d);return ((x-t*b)%a,y)
 seen={(0,0)};Q=deque([(0,0,0)])
 while Q:
  x,y,h=Q.popleft()
  if h==limit:continue
  for dx,dy in [(1,0),(-1,0),(0,1),(0,-1)]:
   v=norm(x+dx,y+dy)
   if v not in seen: seen.add(v);Q.append((*v,h+1))
 return len(seen)==a*d
hnf=0;reject=[]
for s in range(3,15):
 L=2*s+1;p0=next((p for p in range(2,L+1) if L%p==0),L)
 bound=2*s*s if p0==L else (L*L-p0*p0)//2
 for n in range(bound+1,2*s*s+2*s+2):
  for a in range(1,n+1):
   if n%a:continue
   d=n//a
   for b in range(a):
    if gcd(gcd(a,b),d)==1:continue
    hnf+=1
    if diameter(a,b,d,s):reject.append([s,a,b,d])
assert not reject
# Source constructors checked by independent BFS in Z_c x Z_m.
def span(c,m,A,s):
 seen={(0,0)};Q=deque([(0,0,0)])
 while Q:
  x,y,h=Q.popleft()
  if h==s:continue
  for u,v in A:
   for sign in [-1,1]:
    z=((x+sign*u)%c,(y+sign*v)%m)
    if z not in seen:seen.add(z);Q.append((*z,h+1))
 return len(seen)==c*m
constructors=0
for s in range(3,61):
 assert span(s,2*s,[(0,1),(1,1)],s);constructors+=1
 L=2*s+1
 for p in primes:
  if L%p or L==p:continue
  t=L//p;k=(t*t-1)//2;u=(t-1)//2;v=(t+1)//2
  assert span(p,p*k,[(1,u),(1,v)],s);constructors+=1
out={'status':'PASS','row_floor_cases':len(rows),'branches':branches,'q0_cases':sum(q==0 for s,p,q,r,m in rows),'hnf_BFS_above_bound':hnf,'counterexamples':reject,'constructor_BFS_cases':constructors,'exception_s2_p3':next(row for row in rows if row[:2]==[2,3]),'warning':'Finite diagnostics only, not a universal proof.'}
(D/'checker-evidence.json').write_text(json.dumps(out,indent=2));(D/'row-floor-cases.json').write_text(json.dumps(rows));print(json.dumps(out))
