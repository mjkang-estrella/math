#!/usr/bin/env python3
"""Bounded exhaustive diagnostic. Does not prove universal connectivity/mixing."""
from itertools import combinations,permutations
from array import array
from pathlib import Path
import json,sys
n=int(sys.argv[1]) if len(sys.argv)>1 else 7
k=int(sys.argv[2]) if len(sys.argv)>2 else n//2
edges=[(i,j) for i,j in combinations(range(n),2) if not(i%2==0 and j==i+1 and i//2<k)]
index={e:i for i,e in enumerate(edges)}
assert len(edges)<=19,'diagnostic bounded to 2^19 states'
seen=set()
for length in [4,6]:
 for vv in combinations(range(n),length):
  for rest in permutations(vv[1:]):
   if rest[0]>rest[-1]:continue
   v=(vv[0],)+rest
   masks=[0,0]
   for i in range(length):
    e=tuple(sorted((v[i],v[(i+1)%length])))
    if e not in index:break
    masks[i%2]|=1<<index[e]
   else:seen.add(tuple(sorted(masks)))
moves=[(a,a|b) for a,b in seen]
N=1<<len(edges);parent=array('I',range(N))
def root(x):
 while parent[x]!=x:
  parent[x]=parent[parent[x]];x=parent[x]
 return x
transitions=0
for x in range(N):
 for a,toggle in moves:
  if x&toggle!=a:continue
  y=x^toggle
  p,q=root(x),root(y)
  if p!=q:parent[p]=q
  transitions+=1
groups={};bad=[]
weights=[(1<<(4*i))+(1<<(4*j)) for i,j in edges]
degrees=array('Q',[0])*N
for x in range(N):
 if x:
  bit=x&-x;degrees[x]=degrees[x^bit]+weights[bit.bit_length()-1]
 key=degrees[x];r=root(x)
 if key not in groups:groups[key]=(r,x)
 elif groups[key][0]!=r and len(bad)<5:
  bad.append({'degree':[(key>>(4*i))&15 for i in range(n)],'graphs':[[e for i,e in enumerate(edges) if z>>i&1] for z in [groups[key][1],x]]})
out={'n':n,'matching_size':k,'host_edges':len(edges),'states_enumerated':N,'fibers':len(groups),'cycle_masks':len(moves),'undirected_transitions':transitions,'disconnected_examples':bad,'status':'finite diagnostic only; no all-n inference'}
p=Path(__file__).resolve().parent
(p/f'diagnostic-n{n}-k{k}.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
