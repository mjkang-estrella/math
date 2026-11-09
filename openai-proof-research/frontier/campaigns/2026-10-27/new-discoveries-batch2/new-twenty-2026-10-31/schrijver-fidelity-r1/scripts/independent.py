from itertools import combinations
from collections import deque
import json
from pathlib import Path
out={}
for n,k in [(5,2),(7,3)]:
 vs=[s for s in combinations(range(n),k) if all((i+1)%n not in s for i in s)]
 adj=[[j for j,t in enumerate(vs) if i!=j and set(s).isdisjoint(t)] for i,s in enumerate(vs)]
 distances=[]
 for i in range(len(vs)):
  d={i:0};q=deque([i])
  while q:
   a=q.popleft()
   for b in adj[a]:
    if b not in d:d[b]=d[a]+1;q.append(b)
  assert len(d)==len(vs)
  distances.append([d[j] for j in range(len(vs))])
 out[f'{n},{k}']={'vertices':vs,'adjacency':adj,'distances':distances,'diameter':max(map(max,distances))}
out['masks']={str(m):[i for i in range(5) if m & (1<<i)] for m in [0,5,10,17]}
out['stability']={str(s):all((i+1)%5 not in s for i in s) for s in [(0,2),(0,4),(1,2)]}
Path('independent-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
