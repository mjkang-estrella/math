import itertools,json,random,time
from pathlib import Path
L=Path(__file__).resolve().parent
def adjacency(n,edges):
 a=[0]*n
 for u,v in edges:a[u]|=1<<v;a[v]|=1<<u
 return a
def independent(a,I):return all(not(a[v]&I) for v in range(len(a)) if I>>v&1)
def value(a,I):
 n=len(a);S=((1<<n)-1)^I
 if not I or S.bit_count()<2 or not independent(a,I):return n+1
 undom=sum(not(a[v]&I) for v in range(n) if S>>v&1)
 iso=sum(not(a[v]&S) for v in range(n) if S>>v&1)
 return undom+(iso+1)//2
def optimum(a,maximal=False):
 n=len(a);vals=[]
 for I in range(1,1<<n):
  if not independent(a,I):continue
  if maximal and any(not(a[v]&I) for v in range(n) if not I>>v&1):continue
  vals.append((value(a,I),I))
 return min(vals)
def literal_ti(a):
 n=len(a);V=(1<<n)-1
 # Independent test of the actual partition property, no deficit formula.
 for I in range(1,1<<n):
  S=V^I
  if independent(a,I) and all(a[v]&S for v in range(n)) and all(a[v]&I for v in range(n) if S>>v&1):return True
 return False
def direct_min(a):
 n=len(a);missing=[(u,v) for u in range(n) for v in range(u+1,n) if not(a[u]>>v&1)]
 for k in range(len(missing)+1):
  for es in itertools.combinations(missing,k):
   b=a.copy()
   for u,v in es:b[u]|=1<<v;b[v]|=1<<u
   if literal_ti(b):return k
 raise AssertionError('no augmentation')
start=time.monotonic();rows=[]
for n in range(3,7):
 pairs=list(itertools.combinations(range(n),2));count=0;maximum=0
 for mask in range(1<<len(pairs)):
  a=adjacency(n,[e for j,e in enumerate(pairs) if mask>>j&1])
  if min(x.bit_count() for x in a)<(1 if n<=5 else 3):continue
  f,I=optimum(a);d=direct_min(a);assert f==d,(n,mask,f,d)
  if min(x.bit_count() for x in a)>=3:assert 6*f<=n,(n,mask,f)
  count+=1;maximum=max(maximum,f)
 rows.append(dict(n=n,degree_threshold=1 if n<=5 else 3,graphs=count,max_ti=maximum))
rng=random.Random(122);random_rows=[]
for n in range(7,17):
 count=0;worst=0
 for trial in range(100):
  a=adjacency(n,[(u,v) for u in range(n) for v in range(u+1,n) if rng.random()<.38])
  if min(x.bit_count() for x in a)<3:continue
  f,I=optimum(a);assert 6*f<=n,(n,trial,f);count+=1;worst=max(worst,f)
 random_rows.append(dict(n=n,graphs=count,max_ti=worst))
k33=adjacency(6,[(u,v) for u in range(3) for v in range(3,6)])
assert optimum(k33)[0]==1 and optimum(k33,True)[0]==2
crown=adjacency(8,[(u,v) for u in range(4) for v in range(4,8) if v-4!=u])
k44=adjacency(8,[(u,v) for u in range(4) for v in range(4,8)])
assert literal_ti(crown) and not literal_ti(k44)
assert optimum(crown)[0]==0 and optimum(k44)[0]==1
two=adjacency(12,[(u+o,v+o) for o in [0,6] for u in range(3) for v in range(3,6)])
I0=sum(1<<v for v in [0,1,2,6,7,8]);initial=value(two,I0)
neighbors={I0^(1<<v) for v in range(12)}|{I0^(1<<v)^(1<<w) for v in range(12) if I0>>v&1 for w in range(12) if not I0>>w&1}
local=min(value(two,J) for J in neighbors)
assert initial==3 and local==3 and optimum(two)[0]==2
result=dict(exhaustive=rows,random_seed=122,random=random_rows,failed_route_witnesses=dict(maximal_restriction=dict(graph='K3,3',true=1,maximal_cost=2,optimal_I=optimum(k33)[1]),monotonicity=dict(subgraph='K4,4 minus perfect matching',subgraph_ti=0,supergraph='K4,4',supergraph_ti=1)),seconds=time.monotonic()-start,limits='Finite diagnostics, not all-order proof. Direct augmentation independent of deficit optimization on exhaustive graphs only. Random cases check formula value only.')
result['failed_route_witnesses']['strict_local_descent']=dict(graph='two disjoint K3,3',I_mask=I0,initial=initial,best_one_add_delete_or_swap=local,global_optimum=2)
(L/'check-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
