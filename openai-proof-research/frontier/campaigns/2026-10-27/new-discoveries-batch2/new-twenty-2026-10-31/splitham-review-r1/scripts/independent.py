import itertools as it,json,time,hashlib
from pathlib import Path
root=Path(__file__).resolve().parents[1]
def graph(m,B):
    # Literal brief: independent i adjacent clique k iff k-i belongs B.
    return [{v for v in range(2*m) if v!=u and (u<m and v<m or u<m<=v and (u-(v-m))%m in B or v<m<=u and (v-(u-m))%m in B)} for u in range(2*m)]
m=9;r=5;B={0,1,2,3,5}; adj=graph(m,B);n=2*m
assert all(v in adj[u] for u in range(m) for v in range(m) if u!=v)
assert not any(v>=m for u in range(m,n) for v in adj[u])
cut_count=0
for k in range(r):
 for cut in it.combinations(range(n),k):
  left=set(range(n))-set(cut);seen={min(left)};todo=list(seen)
  while todo:
   for v in adj[todo.pop()] & left-seen: seen.add(v);todo.append(v)
  assert seen==left,(cut,seen);cut_count+=1
# Enumerate every possible centre and every six-element subset of its neighbours.
checks=0; leaf_min=100
for u in range(n):
 for leaves in it.combinations(sorted(adj[u]),r+1):
  edges=sum(v in adj[w] for w,v in it.combinations(leaves,2))
  assert edges not in (0,1),(u,leaves,edges)
  leaf_min=min(leaf_min,edges);checks+=1
# Held-Karp path DP, with no independence-count pruning.
# reach[mask] is bitset of possible final vertices for simple paths from vertex 0.
reach=[0]*(1<<n);reach[1]=1
neigh=[sum(1<<v for v in a) for a in adj]
states=0
for mask in range(1,1<<n,2):
 ends=reach[mask]
 while ends:
  bit=ends&-ends;ends-=bit;v=bit.bit_length()-1;states+=1
  available=neigh[v]&~mask
  while available:
   nb=available&-available;available-=nb;reach[mask|nb]|=nb
res={'m':m,'r':r,'B':sorted(B),'edges':sum(map(len,adj))//2,'degrees':list(map(len,adj)), 'cut_tests':cut_count,'forbidden_tests':checks,'minimum_leaf_edges':leaf_min,'dp_states':states,'dp_full_endpoints':[v for v in range(n) if reach[-1]>>v&1], 'no_path_0_1':not bool(reach[-1]&2),'adjacency':[sorted(a) for a in adj]}
assert res['no_path_0_1']
source=root.parent/'expanded-corpus-r156';raw=json.loads((source/'raw/373598.jsonl').read_text());results=json.loads((source/'results.json').read_text())['373598']
res['statement_hash']=hashlib.sha256(raw['statement'].encode()).hexdigest();assert res['statement_hash']==results['statement_sha256']
(root/'outputs/independent.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res),flush=True)
# Exact cyclic regular search, translation normalisation 0 in B suffices.
# Criterion: all distinct clique neighbour sets intersect in >=2. Necessary
# (one clique leaf plus r independent leaves) and sufficient (cases q=0,1,2,>=3).
rob=[]
for r in range(4,9):
 for m in range(r+4,min(r*(r-1)//2+1,20)+1):
  full=(1<<m)-1; tested=0;good=0;first=None
  for tail in it.combinations(range(1,m),r-1):
   b=1+sum(1<<x for x in tail);tested+=1
   if all((b&(((b<<t)|(b>>(m-t)))&full)).bit_count()>=2 for t in range(1,m)):
    good+=1
    if first is None:first=[0,*tail]
  row={'r':r,'m':m,'order':2*m,'tested_0_normalized':tested,'good':good,'first':first};rob.append(row);print(json.dumps(row),flush=True)
(root/'outputs/robustness.json').write_text(json.dumps(rob,indent=2)+'\n')
