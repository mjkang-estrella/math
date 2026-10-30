"""Exact small-graph controls, not an all-order theorem. No floating point."""
import json,itertools,collections
from pathlib import Path
L=Path(__file__).resolve().parent
def connected(E,n=None):
 V=set(range(n)) if n is not None else set(itertools.chain.from_iterable(E))
 if not V:return False
 seen={min(V)}
 while True:
  new=seen|{v for u,v in E if u in seen}|{u for u,v in E if v in seen}
  if new==seen:return seen==V
  seen=new
def shortest(n,E):
 d=tuple(sum(v in e for e in E) for v in range(n))
 adj=[[] for _ in range(n)]
 for i,(u,v) in enumerate(E):adj[u].append((v,i));adj[v].append((u,i))
 def good(a):return all(d[u]+a[u]!=d[v]+a[v] for u,v in E)
 z=(0,)*n
 if good(z):return [],0
 q=collections.deque();prev={}
 for s in range(n):q.append((s,z));prev[(s,z)]=None
 end=None
 while q:
  s,a=q.popleft()
  for t,i in adj[s]:
   b=list(a);b[s]+=1;b[t]+=1;b=tuple(b);st=(t,b)
   if st in prev:continue
   prev[st]=((s,a),i)
   if good(b):end=st;break
   # Source 4m bound ensures eventual success; stop strictly at that bound.
   if sum(b)//2<4*len(E):q.append(st)
  if end:break
 assert end is not None
 edges=[]
 while prev[end] is not None:
  old,i=prev[end];edges.append(i);end=old
 edges.reverse();return edges,len(prev)
def validate(n,E,W):
 x=[W.count(i) for i in range(len(E))];d=[sum(v in e for e in E) for v in range(n)];a=[sum(x[i] for i,e in enumerate(E) if v in e) for v in range(n)]
 assert all(d[u]+a[u]!=d[v]+a[v] for u,v in E)
 assert sum(a)==2*len(W) and sum(v%2 for v in a) in [0,2]
 if W:
  assert connected([E[i] for i in W])
 return x
rows=[]
for n in range(3,6):
 pairs=list(itertools.combinations(range(n),2))
 for mask in range(1<<len(pairs)):
  E=[e for i,e in enumerate(pairs) if mask>>i&1]
  if not connected(E,n):continue
  W,states=shortest(n,E);x=validate(n,E,W)
  assert len(W)<=3*len(E)
  rows.append(dict(n=n,edges=E,minimum=len(W),multiplicities=x,walk_edge_indices=W,states=states))
# Explicit failure of the tempting direct 1-2-3 -> walk conversion.
# P4 proper weights (1,2,1): added counts (0,1,0) are a walk, but
# another proper weighting (2,1,3) has disconnected positive added support.
E=[(0,1),(1,2),(2,3)];w=[2,1,3]
s=[sum(w[i] for i,e in enumerate(E) if v in e) for v in range(4)]
assert all(s[u]!=s[v] for u,v in E)
assert not connected([E[i] for i in range(3) if w[i]>1])
# Connected support alone does not suffice: four odd-degree vertices.
E2=[(0,1),(0,2),(0,3)];w2=[2,2,2]
s2=[sum(w2[i] for i,e in enumerate(E2) if v in e) for v in range(4)]
assert all(s2[u]!=s2[v] for u,v in E2)
assert sum(sum(1 for e in E2 if v in e)%2 for v in range(4))==4
out=dict(scope='All connected labeled simple graphs on 3..5 vertices; BFS exhausts all shorter walk states. Diagnostics only.',graphs=len(rows),by_order=dict(collections.Counter(r['n'] for r in rows)),maximum_ratio=max((r['minimum']/len(r['edges']) for r in rows)),records=rows,conversion_objections=[dict(edges=E,proper_weights=w,weighted_degrees=s,obstruction='Disconnected support of w-1'),dict(edges=E2,proper_weights=w2,weighted_degrees=s2,obstruction='Four odd vertices in w-1')])
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='records'}))
