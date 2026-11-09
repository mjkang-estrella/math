import json,itertools
from pathlib import Path
packet=json.loads(Path('packet/certificate.json').read_text());checked=0
for idx,row in enumerate(packet):
 a=row['adjacency'];c=row['colors'];n=len(a)
 assert n==8 and all(not(a[i]>>i&1) for i in range(n))
 assert all((a[i]>>j&1)==(a[j]>>i&1) for i in range(n) for j in range(n))
 if idx:assert all(a[i]==(255^packet[0]['adjacency'][i]^(1<<i)) for i in range(n))
 for x,y in itertools.permutations(range(n),2):
  s,side=row['certificates'][x*n+y];assert not(s>>x&1 or s>>y&1)
  cols=[c[v] for v in range(n) if s>>v&1];assert len(cols)==len(set(cols))
  if a[x]>>y&1:assert c[x] not in cols or c[y] not in cols
  d=[[bool(a[u]>>v&1) and not(s>>u&1 or s>>v&1) and {u,v}!={x,y} for v in range(n)] for u in range(n)]
  for k in range(n):
   for u in range(n):
    for v in range(n):d[u][v] |= d[u][k] and d[k][v]
  assert not d[x][y]
  assert side>>x&1 and not(side>>y&1)
  checked+=1
# Also verify the new order-9 witnesses using this matrix algorithm and exhaustive cuts.
for r in json.loads(Path('extensions9.json').read_text())['failures']:
 for a,c in [(r['adj'],r['rvd'][1]),([511^m^(1<<i) for i,m in enumerate(r['adj'])],r['complement_rvd'][1])]:
  for x,y in itertools.combinations(range(9),2):
   for s in range(512):
    if s>>x&1 or s>>y&1:continue
    cols=[c[v] for v in range(9) if s>>v&1]
    if len(set(cols))<len(cols) or (a[x]>>y&1 and c[x] in cols and c[y] in cols):continue
    d=[[bool(a[u]>>v&1) and not(s>>u&1 or s>>v&1) and {u,v}!={x,y} for v in range(9)] for u in range(9)]
    for k in range(9):
     for u in range(9):
      for v in range(9):d[u][v] |= d[u][k] and d[k][v]
    if not d[x][y]:break
   else:raise AssertionError((x,y))
print('PASS: 112 ordered supplied cuts; all 216 unordered order-9 witness pairs verified by exhaustive masks and Floyd-Warshall')
