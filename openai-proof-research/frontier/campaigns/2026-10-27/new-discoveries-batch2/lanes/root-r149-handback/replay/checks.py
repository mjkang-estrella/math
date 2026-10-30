import json,itertools,hashlib
from pathlib import Path
L=Path(__file__).resolve().parent
def windmill(q,t):
 n=1+q*t;adj=[0]*n
 for k in range(q):
  block=[0]+list(range(1+k*t,1+(k+1)*t))
  for a,b in itertools.combinations(block,2):adj[a]|=1<<b;adj[b]|=1<<a
 return adj
def independent_records(adj,d):
 # ALL independent subsets via increasing-bit recursion; no size cutoff.
 n=len(adj);records=[]
 def visit(a,candidates,nb):
  if a:
   assert 2*nb.bit_count()>(d-2)*a.bit_count()
   records.append((a,nb))
  while candidates:
   bit=candidates&-candidates;candidates-=bit;v=bit.bit_length()-1
   visit(a|bit,candidates&~adj[v],nb|adj[v])
 visit(0,(1<<n)-1,0)
 return records
out={'windmills':[],'strict_exchange':[]}
for d in range(5,11):
 t=(d+1)//2;q=7;adj=windmill(q,t);n=len(adj)
 rec=independent_records(adj,d)
 assert max(a.bit_count() for a,b in rec)==q
 # Explicit spanning tree: one Hamilton arm in each clique petal.
 tree=[[] for _ in adj]
 for k in range(q):
  path=[0]+list(range(1+k*t,1+(k+1)*t))
  for a,b in zip(path,path[1:]):
   assert adj[a]>>b&1;tree[a].append(b);tree[b].append(a)
 leaves=[v for v in range(n) if len(tree[v])==1];assert len(leaves)==q
 leafd=[]
 for a in leaves:
  ds={a:0};queue=[a]
  for v in queue:
   for u in tree[v]:
    if u not in ds:ds[u]=ds[v]+1;queue.append(u)
  assert len(ds)==n
  leafd.extend(ds[b] for b in leaves if b>a)
 assert min(leafd)==2*t>=d
 assert n>3*d
 out['windmills'].append(dict(d=d,q=q,t=t,n=n,independent_sets=len(rec),minimum_leaf_distance=min(leafd),independent_records_sha256=hashlib.sha256(json.dumps(rec).encode()).hexdigest()))
# Direct original isolated-vertex condition for all nonempty S in W(6,3).
adj=windmill(6,3);n=len(adj);full=(1<<n)-1;checked=0
for s in range(1,full+1):
 remaining=full^s;i=sum(1 for v in range(n) if remaining>>v&1 and not adj[v]&remaining)
 assert 3*i<2*s.bit_count();checked+=1
out['all_subsets_d5']=dict(n=n,subsets=checked)
# Every one-edge exchange from the spanning star of K_n stalls min leaf distance.
for n in range(6,11):
 c=0
 for a,b in itertools.combinations(range(1,n),2):
  for removed in [a,b]:
   degrees=[n-2]+[1]*(n-1);degrees[removed]=1;degrees[b if removed==a else a]=2
   untouched=[v for v in range(1,n) if v not in [a,b]]
   assert len(untouched)>=2 # these remain leaves sharing the center
   c+=1
 out['strict_exchange'].append(dict(n=n,all_exchanges=c,minimum_leaf_distance=2))
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
