from pathlib import Path
from fractions import Fraction as F
from itertools import product
import json, collections,datetime
out=Path(__file__).resolve().parent
alpha=(F(1,1000),F(7,27),F(1,3))
def compute(n,edges):
 adj=[set() for _ in range(n)]
 for u,v in edges:adj[u].add(v);adj[v].add(u)
 dist={0:0,1:0};q=collections.deque(dist)
 while q:
  u=q.popleft()
  for v in adj[u]:
   if v not in dist:dist[v]=dist[u]+1;q.append(v)
 assert len(dist)==n
 maxima=[];size=-1
 for mask in range(1<<n):
  if any((mask>>u)&(mask>>v)&1 for u,v in edges):continue
  k=mask.bit_count()
  if k>size:size=k;maxima=[]
  if k==size:maxima.append(mask)
 e=tuple(F(sum(sum(bool(m>>v&1) for v in range(n) if dist[v]==i) for m in maxima),len(maxima)) for i in range(3))
 value=sum(a*b for a,b in zip(alpha,e))
 return dict(n=n,edges=edges,depth=max(dist.values()),max_size=size,maxima=[[v for v in range(n) if m>>v&1] for m in maxima],e=list(map(str,e)),value=str(value)),value
p,pv=compute(8,[(0,1),(0,2),(0,3),(1,5),(1,7),(3,4),(4,6),(5,6)])
rows=[]
for counts in product(range(3),repeat=4):
 edges=[(0,1),(0,2),(0,3),(1,4),(1,5)];n=6
 for branch,k in enumerate(counts,2):
  for _ in range(k):edges.append((branch,n));n+=1
 row,val=compute(n,edges);row['counts']=counts;rows.append(row)
 assert val>=1
minimum=min(F(r['value']) for r in rows)
assert p['e']==['2/5','14/5','4/5'] and pv==F(67027,67500) and minimum==F(3001,3000)
# The sole shallower root-cubic tree has four leaf branches and no layer 2.
assert rows[0]['depth']==1 and rows[0]['value']=='28/27'
assert sum(a*F(e) for a,e in zip((F(1,2),F(13,44),F(3,44)),p['e']))==F(119,110)
(out/'independent-math.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pattern':p,'trees':rows,'minimum':str(minimum),'minimizers':[r['counts'] for r in rows if F(r['value'])==minimum],'depth_1_value':rows[0]['value'],'controls':{'wrong_pattern_value_rejected':pv!=1,'all_tree_values_strict':minimum>1}},indent=2)+'\n')
print('81 forms checked; minimum',minimum,'pattern',pv)
