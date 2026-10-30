from itertools import combinations
from math import comb
import json

def graphs(n,d):
 adj=[0]*n; rem=[d]*n
 def go(v):
  if v==n:
   yield tuple(adj);return
  if rem[v]<0:return
  avail=[j for j in range(v+1,n) if rem[j]>0]
  if rem[v]>len(avail):return
  for ss in combinations(avail,rem[v]):
   a=adj[v]
   for j in ss:adj[v]|=1<<j;adj[j]|=1<<v;rem[j]-=1
   if all(rem[j]<=sum(rem[k]>0 for k in range(v+1,n) if k!=j) for j in range(v+1,n)):
    yield from go(v+1)
   for j in ss:adj[j]^=1<<v;rem[j]+=1
   adj[v]=a
 yield from go(0)
def stat(a):
 n=len(a);tri=sum((a[i]&a[j]).bit_count() for i in range(n) for j in range(i+1,n) if a[i]>>j&1)//3
 holes=sum(comb(x.bit_count(),2) for x in a)-3*tri
 clique=False
 for v in range(n):
  S=a[v]|1<<v
  if all((a[j]&S).bit_count()==S.bit_count()-1 for j in range(n) if S>>j&1):clique=True
 return tri,holes,clique
rows=[];total=0;mx={}
for n in range(1,9):
 for d in range((n-1)//2+1):
  if n*d%2:continue
  cnt=0;data={d:[],n-1-d:[]}
  for a in graphs(n,d):
   cnt+=1
   for e in data:
    b=a if e==d else tuple(((1<<n)-1)^(1<<i)^a[i] for i in range(n))
    t,h,c=stat(b);assert h==n*comb(e,2)-3*t
    data[e].append((t,c))
  total+=cnt
  for e,vals in data.items():
   if not vals:continue
   best=max(t for t,c in vals);mx[n,e]=best
   rows.append(dict(n=n,d=e,labeled=cnt,max_triangles=best,optima_without_clique=sum(t==best and not c for t,c in vals)))
assert next(r['labeled'] for r in rows if r['n']==4 and r['d']==1)==3
assert next(r['labeled'] for r in rows if r['n']==6 and r['d']==3)==70
comparisons=[]
for (n,d),t in mx.items():
 if (n+d+1,d) in mx:
  assert mx[n+d+1,d]==t+comb(d+1,3)
  comparisons.append([n,d,n+d+1])
# Two K4, remove one edge in each and cross reconnect: regular, no K4 component;
# four untouched vertices have neighborhood deficit 1, defeating an unconditional gap-2 rule.
a=[0]*8
for S in [range(4),range(4,8)]:
 for i,j in combinations(S,2):a[i]|=1<<j;a[j]|=1<<i
for i,j in [(0,1),(4,5)]:a[i]^=1<<j;a[j]^=1<<i
for i,j in [(0,4),(1,5)]:a[i]|=1<<j;a[j]|=1<<i
assert all(x.bit_count()==3 for x in a)
t,h,c=stat(a);assert not c and t==4
local=[3-sum((a[i]&a[j]).bit_count() for j in range(8) if a[i]>>j&1)//2 for i in range(8)]
assert sorted(local)==[1,1,1,1,2,2,2,2]
# Independent edge-mask census guards recursive enumeration completeness at small orders.
from collections import Counter
mask_controls=0
for n in range(1,6):
 es=list(combinations(range(n),2)); got={d:Counter() for d in range(n)}
 for mask in range(1<<len(es)):
  a=[0]*n
  for k,(i,j) in enumerate(es):
   if mask>>k&1:a[i]|=1<<j;a[j]|=1<<i
  ds=[x.bit_count() for x in a]
  if len(set(ds))==1:got[ds[0]][stat(a)]+=1
  mask_controls+=1
 for d in range(n):assert got[d]==Counter(stat(a) for a in graphs(n,d))
print(json.dumps(dict(status='PASS',independent_mask_controls=mask_controls,enumerated_labeled_base_graphs=total,extremal_rows=rows,periodicity_comparisons=comparisons,method_countermodel=dict(adjacency=a,triangles=t,local_missing_pairs=local),limit='All feasible regular classes through order8 only. No universal theorem follows.'),indent=2))
