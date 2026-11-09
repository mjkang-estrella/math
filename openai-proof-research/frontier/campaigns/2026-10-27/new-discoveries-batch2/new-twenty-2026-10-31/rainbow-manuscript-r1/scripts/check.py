from pathlib import Path
import json,itertools,hashlib
P=Path(__file__).resolve().parents[1]
data=json.loads((P/'evidence/original/outputs/rainbow-certificate.json').read_text()); checks=[]
for d in data:
 a=d['adjacency']; c=d['colors']; n=len(a)
 assert all(not (a[i]>>i&1) and all((a[i]>>j&1)==(a[j]>>i&1) for j in range(n)) for i in range(n))
 for x,y in itertools.combinations(range(n),2):
  s,A=d['certificates'][8*x+y]; S=[v for v in range(n) if s>>v&1]
  assert not s>>x&1 and not s>>y&1 and A>>x&1 and not A>>y&1
  assert len({c[v] for v in S})==len(S)
  assert not (a[x]>>y&1) or c[x] not in [c[v] for v in S] or c[y] not in [c[v] for v in S]
  for u in range(n):
   for v in range(n):
    if A>>u&1 and not A>>v&1 and not s>>u&1 and not s>>v&1 and {u,v}!={x,y}: assert not a[u]>>v&1
 edges=[(i,j) for i,j in itertools.combinations(range(n),2) if (a[i]&a[j]).bit_count()>=2]
 cliques=[q for k in [3,4] for q in itertools.combinations(range(n),k) if all((i,j) in edges for i,j in itertools.combinations(q,2))]
 checks.append({'verified_unordered_cuts':28,'common_neighbor_conflicts':edges,'cliques':cliques})
assert data[1]['adjacency']==[255^a^(1<<i) for i,a in enumerate(data[0]['adjacency'])]
(P/'independent-check.json').write_text(json.dumps(checks,indent=2)+'\n');print(json.dumps(checks))
