from pathlib import Path
from itertools import combinations,permutations
import json,math
P=Path(__file__).resolve().parent
def sup(a,o):
 cover=0
 for v,ne in enumerate(a):
  if not (o>>v&1):
   t=ne&o
   if t and not(t&(t-1)):cover|=t
 return cover==o
def saving(a):
 n=len(a)
 for k in range(n//2,-1,-1):
  for c in combinations(range(n),k):
   o=sum(1<<v for v in c)
   if sup(a,o):return k,o
factors=[]
for n in range(2,6):
 es=list(combinations(range(n),2));seen=set()
 for mask in range(1<<len(es)):
  a=[0]*n
  for k,(u,v) in enumerate(es):
   if mask>>k&1:a[u]|=1<<v;a[v]|=1<<u
  reach=1
  while True:
   r=reach
   for v in range(n):
    if reach>>v&1:reach|=a[v]
   if r==reach:break
  if reach!=(1<<n)-1:continue
  can=min(sum((1<<k) for k,(u,v) in enumerate(es) if a[p[u]]>>p[v]&1) for p in permutations(range(n)))
  if can in seen:continue
  seen.add(can);s,o=saving(a);factors.append(dict(n=n,adj=a,gamma=n-s))
results=[]
for i,g in enumerate(factors):
 for j,h in enumerate(factors[i:],i):
  n=g['n'];m=h['n'];rhs=g['gamma']*h['gamma'];N=n*m
  if n==m==5:continue
  if rhs<=(N+1)//2:results.append(dict(i=i,j=j,method='injection half-order bound',rhs=rhs));continue
  a=[]
  for x in range(n):
   for y in range(m):a.append(sum(1<<(z*m+y) for z in range(n) if g['adj'][x]>>z&1)|sum(1<<(x*m+z) for z in range(m) if h['adj'][y]>>z&1))
  k=N-rhs+1;count=0;witness=None
  for c in combinations(range(N),k):
   count+=1;o=sum(1<<v for v in c)
   if sup(a,o):witness=o;break
  results.append(dict(i=i,j=j,method='exact forbidden-size complement enumeration',rhs=rhs,outside_size=k,subsets=count,counterexample=witness))
  print(i,j,N,count,witness,flush=True)
# exact obstruction to the count-only witness relaxation: K4 square, n=m=4, pG=pH=1.
# 4 horizontal tokens and 4 vertical tokens can be placed disjointly at different cells.
H=[(i,i) for i in range(4)];V=[(i,(i+1)%4) for i in range(4)]
assert set(H).isdisjoint(V) and len(H)+len(V)==8>4+4-1
# Row-by-row super domination fails even for the literal K2 x K3 half-size witness.
a=[sum(1<<(x*3+z) for z in range(3) if z!=y)|(1<<((1-x)*3+y)) for x in range(2) for y in range(3)]
assert sup(a,0b111000)
(P/'check-results.json').write_text(json.dumps(dict(factors=factors,pairs=results,relaxation_obstruction=dict(horizontal=H,vertical=V,relaxed_outside=8,conjectured_max_outside=7),empty_row_witness=0b111000),indent=2))
print('complete',len(factors),len(results),sum(x.get('subsets',0) for x in results),flush=True)
