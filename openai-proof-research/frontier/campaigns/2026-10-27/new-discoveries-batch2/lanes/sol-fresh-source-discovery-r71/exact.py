from itertools import combinations,product
from math import gcd
from functools import reduce
from heapq import heappush,heappop
import json,pathlib
root=pathlib.Path(__file__).parent

def apery(a):
 m=a[0];d=[10**12]*m;d[0]=0;q=[(0,0)]
 while q:
  v,i=heappop(q)
  if v!=d[i]:continue
  for x in a[1:]:
   j=(i+x)%m;w=v+x
   if w<d[j]:d[j]=w;heappush(q,(w,j))
 return d

def inside(x,w):return x>=0 and x>=w[x%len(w)]
def pf(a,w):return sorted(x-a[0] for x in w if all(inside(x-a[0]+b,w) for b in a))
def facts(a,h):
 if not a:return [()] if h==0 else []
 return [(i,)+q for i in range(h//a[0]+1) for q in facts(a[1:],h-i*a[0])]
def info(a,w,p):
 n=len(a);alpha=p[1]-p[0];h=p[0]-alpha
 if h<0:return {'a':a,'h':h,'pf':p,'skip':'negative h, formulation not pursued'}
 z=facts(a,h);assert z
 M=[max(q[i] for q in z) for i in range(n)]
 assert all((not inside(c+alpha,w))==(inside(h-c,w)) for c in range(h+1) if inside(c,w))
 for i,x in enumerate(a):
  assert not inside(M[i]*x+alpha,w) and inside((M[i]+1)*x+alpha,w)
 T=[[j for j,b in enumerate(a) if inside((M[i]+1)*a[i]+alpha-b,w)] for i in range(n)]
 row={'a':a,'pf':p,'h':h,'alpha':alpha,'factorizations':z,'M':M,'hprime':sum(x*y for x,y in zip(M,a)),'T':T}
 if len(z)==1:
  assert all(len(t)==1 for t in T);succ=[t[0] for t in T];cyc=[0]
  while succ[cyc[-1]]!=0:cyc.append(succ[cyc[-1]]);assert len(cyc)<=n
  assert len(cyc)==n
  for i in range(n):assert ((M[i]+1)*a[i]+alpha)%a[succ[i]]==0
 return row

stats={};selected=[];nonunique=[];checks=0
for n,hi in [(4,42),(5,34),(6,26)]:
 count=eligible=ap=nonneg=0
 for a in combinations(range(n,hi+1),n):
  count+=1
  if reduce(gcd,a)!=1:continue
  # minimality via finite coin DP
  d=[False]*(a[-1]+1);d[0]=True;ok=True
  for x in a:
   if d[x]:ok=False;break
   for j in range(x,len(d)):d[j]|=d[j-x]
  if not ok:continue
  eligible+=1;w=apery(a);p=pf(a,w)
  if len(p)!=n-1 or len(set(p[i+1]-p[i] for i in range(n-2)))!=1:continue
  ap+=1;row=info(a,w,p)
  if row['h']>=0:
   nonneg+=1;checks+=1
   if len(row['factorizations'])>1:nonunique.append(row)
   if len(selected)<12:selected.append(row)
 stats[n]={'tuples':count,'minimal_coprime':eligible,'AP_type_n_minus_1':ap,'nonnegative_h':nonneg}
 print(n,stats[n],flush=True)
 # preserve each shard's work even if later interrupted
 (root/'logs/exact-partial.json').write_text(json.dumps({'stats':stats,'selected':selected,'nonunique':nonunique},indent=2))
# Cross-check Dijkstra/PF with direct membership for all modest semigroups, independent loops.
independent=0
for a in combinations(range(4,19),4):
 if reduce(gcd,a)!=1:continue
 w=apery(a);F=max(w)-a[0];reach=[False]*(F+2*a[-1]+1);reach[0]=True
 for s in range(1,len(reach)):reach[s]=any(s>=x and reach[s-x] for x in a)
 pp=[s for s in range(1,F+1) if not reach[s] and all(reach[s+x] for x in a)]
 assert pp==pf(a,w)
 assert all(reach[s]==inside(s,w) for s in range(len(reach)))
 independent+=1
# Actual source examples and a false generalization without the PF-AP premise.
examples=[]
for a in [(17,40,42,45),(7,15,16,17),(6,7,8,9)]:
 w=apery(a);p=pf(a,w);examples.append({'a':a,'apery':w,'pf':p})
result={'stats':stats,'boundary_cycle_checks':checks,'independent_membership_PF':independent,'selected':selected,'nonunique':nonunique,'examples':examples,'note':'Finite exact evidence only; no all-semigroup theorem.'}
(root/'logs/exact-result.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k not in ('selected','nonunique')},indent=2))
