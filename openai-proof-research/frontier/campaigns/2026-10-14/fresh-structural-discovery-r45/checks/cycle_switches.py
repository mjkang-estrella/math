#!/usr/bin/env python3
"""Exact finite route obstruction; no claim about the spectral target."""
import json

def edge(a,b): return tuple(sorted((a,b)))
def comps(edges,n):
 adj=[set() for _ in range(n)]
 for a,b in edges: adj[a].add(b);adj[b].add(a)
 assert all(len(x)==2 for x in adj)
 unseen=set(range(n));ans=[]
 while unseen:
  stack=[min(unseen)];seen=set()
  while stack:
   x=stack.pop()
   if x in seen: continue
   seen.add(x);stack.extend(adj[x]-seen)
  unseen-=seen;ans.append(sorted(seen))
 return ans
n=8
base={edge(i,(i+1)%n)for i in range(n)}
switches=[({edge(0,1),edge(4,5)},{edge(0,4),edge(1,5)}),({edge(2,3),edge(6,7)},{edge(2,6),edge(3,7)})]
assert {x for e in switches[0][0]for x in e}.isdisjoint({x for e in switches[1][0]for x in e})
individual=[comps((base-old)|new,n)for old,new in switches]
assert all(len(c)==1 for c in individual)
combined=base.copy()
for old,new in switches:
 assert old<=combined and not new&combined
 combined=(combined-old)|new
answer=comps(combined,n)
assert answer==[[0,3,4,7],[1,2,5,6]]
print(json.dumps(dict(status='PASS',interpretation='individually Hamilton-cycle-preserving vertex-disjoint switches need not jointly preserve that cycle',individual_components=individual,combined_components=answer),indent=2))
