"""Exact closed components for the edge-grading collision; stdout only."""
from itertools import combinations
from collections import deque
import json
h=(2,4,4,5,5)
def edge(a,b):return a!=b and max(a,b)<=h[min(a,b)-1]
def neighbors(w):
 for i in range(4):
  a,b=w[i:i+2]
  if not edge(a,b):yield w[:i]+(b,a)+w[i+2:]
 for i in range(3):
  z=w[i:i+3];a,b,c=sorted(z)
  if edge(a,b) and edge(b,c) and not edge(a,c):
   for x,y in [((b,a,c),(a,c,b)),((b,c,a),(c,a,b))]:
    if z==x:yield w[:i]+y+w[i+3:]
    if z==y:yield w[:i]+x+w[i+3:]
def component(start):
 C={start};q=deque([start])
 while q:
  for w in neighbors(q.popleft()):
   if w not in C:C.add(w);q.append(w)
 return C
A=component((1,2,3,5,4));B=component((1,3,2,4,5))
assert len(A)==len(B)==6 and A.isdisjoint(B)
for C in (A,B):
 assert all(set(neighbors(w))<=C for w in C)
 assert all(sum(a>b and edge(a,b) for i,a in enumerate(w) for b in w[i+1:])==1 for w in C)
edges=[(a,b) for a,b in combinations(range(1,6),2) if edge(a,b)];par={e:e for e in edges}
def find(e):
 while e!=par[e]:e=par[e]
 return e
constraints=[]
for a,b,c in combinations(range(1,6),3):
 if edge(a,b) and edge(b,c) and not edge(a,c):
  par[find((a,b))]=find((b,c));constraints.append([[a,b],[b,c]])
assert len({find(e) for e in edges})==1
print(json.dumps({'h':h,'components':[sorted(A),sorted(B)],'edge_weight_equalities':constraints,'conclusion':'two different closed local-flip classes, identical scalar and all permitted independent-edge quantum grades; no negative class coefficient or general impossibility claimed'},indent=2))
