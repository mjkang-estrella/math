from itertools import combinations_with_replacement,combinations
from collections import deque
import json
from pathlib import Path
O=Path(__file__).parent
n=10
V=list(combinations_with_replacement(range(n),2))
R=[(i,i+1) for i in (0,1,2,3,5,6,7,8)]
def distance(x,y):
 return 2-sum(min(x.count(i),y.count(i)) for i in range(n))
signatures={x:tuple(distance(x,r) for r in R) for x in V}
assert len(set(signatures.values()))==55
def legal_neighbors(x):
 result=set()
 for token in (0,1):
  for destination in range(n):
   if destination!=x[token]:
    y=list(x);y[token]=destination;result.add(tuple(sorted(y)))
 return result
edges={x:legal_neighbors(x) for x in V}
tested=0
for x in V:
 d={x:0};q=deque([x])
 while q:
  a=q.popleft()
  for b in edges[a]:
   if b not in d:d[b]=d[a]+1;q.append(b)
 assert len(d)==55
 for y in V:assert d[y]==distance(x,y);tested+=1
local_columns=[(1,0,0,0),(1,1,0,0),(0,1,1,0),(0,0,1,1),(0,0,0,1)]
local={('single',i):c for i,c in enumerate(local_columns)}
local.update({('pair',i,j):tuple(a+b for a,b in zip(local_columns[i],local_columns[j])) for i,j in combinations(range(5),2)})
assert len(set(local.values()))==15
assert [distance((1,1),r) for r in [(0,1),(1,2)]]==[distance((0,2),r) for r in [(0,1),(1,2)]]
report={'n':n,'k':2,'vertices':len(V),'landmarks_1based':[[i+1,j+1] for i,j in R], 'distinct_signatures':len(set(signatures.values())),'BFS_distance_pairs':tested,'local_nonempty_supports':len(local),'bound':8,'conjectured':9}
(O/'exact-results.json').write_text(json.dumps(report,indent=2)+'\n')
with open(O/'signatures.jsonl','w') as f:
 for x,s in signatures.items():f.write(json.dumps({'vertex_1based':[i+1 for i in x],'distances':s})+'\n')
print(json.dumps(report))
