import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1')
from fractions import Fraction as Q
from itertools import product, combinations
from pathlib import Path
import json
def solve(M,b):
 a=[[Q(x) for x in row]+[Q(y)] for row,y in zip(M,b)]
 for i in range(3):
  k=next((k for k in range(i,3) if a[k][i]),None)
  if k is None:return None
  a[i],a[k]=a[k],a[i];q=a[i][i];a[i]=[x/q for x in a[i]]
  for k in range(3):
   if k!=i:
    q=a[k][i];a[k]=[x-q*y for x,y in zip(a[k],a[i])]
 return [row[3] for row in a]
def mis(verts,m):
 adj={v:[w for w in [((v[0]+1)%m,v[1]),((v[0]-1)%m,v[1]),(v[0],(v[1]+1)%m),(v[0],(v[1]-1)%m)] if w in verts] for v in verts};color={}
 for v in verts:
  if v in color:continue
  color[v]=0;queue=[v]
  for x in queue:
   for y in adj[x]:
    if y not in color:color[y]=1-color[x];queue.append(y)
    else:assert color[y]!=color[x]
 matched={}
 def aug(x,seen):
  for y in adj[x]:
   if y in seen:continue
   seen.add(y)
   if y not in matched or aug(matched[y],seen):matched[y]=x;return True
  return False
 n=sum(aug(x,set()) for x in verts if color[x]==0)
 return len(verts)-n
D=Path.cwd()
results=[]
for t in range(1,5):
 m=2*t+1
 subsets=[{i for i in range(m) if mask>>i&1} for mask in range(1<<m) if all(not(mask>>i&1 and mask>>((i+1)%m)&1) for i in range(m))]
 profiles={(1,0,m*t),(0,0,m*t)}
 # Enumerate every pair of possible mixed layers, compute remaining grid MIS by matching.
 for A,B in product(subsets,repeat=2):
  if not A or not B:r=t*(m-len(A or B))
  else:
   verts={(i,j) for i in range(m) for j in range(m) if i not in A and j not in B}
   r=mis(verts,m)
  assert r+len(A)+len(B) <= t*m+1+(1-t)*len(A)
  assert r+len(A)+len(B) <= t*m+1+(1-t)*len(B)
  profiles.add((0,len(A)+len(B),r))
 P=sorted(profiles); sizes=[1,2*m,m*m]
 # Enumerate all basic primal solutions with three positive profiles.
 best=None
 for ids in combinations(range(len(P)),3):
  x=solve([[P[j][i] for j in ids] for i in range(3)],sizes)
  if x is None or min(x)<0:continue
  if best is None or sum(x)<best[0]:best=(sum(x),ids,x)
 assert best is not None
 _,ids,x=best;primal=[Q(0)]*len(P)
 for j,w in zip(ids,x):primal[j]=w
 dual=solve([P[j] for j in ids],[1,1,1]);assert min(dual)>=0
 assert all(sum(dual[i]*p[i] for i in range(3))<=1 for p in P)
 assert all(sum(primal[j]*P[j][i] for j in range(len(P)))>=sizes[i] for i in range(3))
 value=sum(primal); assert value==sum(dual[i]*sizes[i] for i in range(3))==Q(6*t*t+7*t+3,2*t*t+t+1)
 results.append(dict(t=t,chi=str(value),dual=list(map(str,dual)),positive_primal=[dict(profile=P[j],weight=str(w)) for j,w in enumerate(primal) if w],profiles=P,pairs=len(subsets)**2,exact_rational_certificate=True))
(D/'receipts/independent-lp.json').write_text(json.dumps(results,indent=2))
coverage=[]
for t in range(1,7):
 m=2*t+1;den=2*t*t+t+1;V=list(product(range(-1,m),repeat=2));cov={v:Q(0) for v in V};counts=[0,0,0]
 def alt(i):return i% m<2*t and (i%m)%2==0
 def adj1(x,y):return x!=y and (x==-1 or y==-1 or (x-y)%m in (1,m-1))
 def check(S,k,w):
  counts[k]+=1
  for x,y in product(S,repeat=2):assert not ((x[0]==y[0] and adj1(x[1],y[1])) or (x[1]==y[1] and adj1(x[0],y[0])))
  for v in S:cov[v]+=w
 for s in range(m):check({(-1,-1)}|{(i,j) for i in range(m) for j in range(m) if alt(i-j-s)},0,Q(1,m))
 for a,b in product(range(m),repeat=2):
  for c in range(2):check({(a,-1),(-1,b)}|{(i,j) for i in range(m) for j in range(m) if i!=a and j!=b and (((i-a-1)%m+(j-b-1)%m)%2==c)},1,Q(1,2*m*den))
  check({(i,-1) for i in range(m) if alt(i-a)}|{(-1,j) for j in range(m) if alt(j-b)}|{(i,j) for i in range(m) for j in range(m) if not alt(i-a) and not alt(j-b) and (((i-a)%m==2*t)==((j-b)%m==2*t))},2,Q(1,den))
 assert set(cov.values())=={Q(1)}
 total=Q(counts[0],m)+Q(counts[1],2*m*den)+Q(counts[2],den)
 assert total==Q(6*t*t+7*t+3,den)
 coverage.append(dict(t=t,family_counts=counts,vertices=len(V),every_index_independent=True,every_vertex_coverage='1',total=str(total)))
(D/'receipts/independent-coverage.json').write_text(json.dumps(coverage,indent=2))
print(json.dumps(dict(lp=results,coverage=coverage)))
