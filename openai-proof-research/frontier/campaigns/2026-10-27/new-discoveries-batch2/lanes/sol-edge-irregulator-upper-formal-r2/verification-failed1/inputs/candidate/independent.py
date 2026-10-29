import itertools,json,pathlib
b=pathlib.Path(__file__).resolve().parent
# a,b,c,d,x,y,h = 0,...,6
edges=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,4),(4,5),(5,6)]
def valid(n,ee):
 d=[0]*n
 for u,v in ee:d[u]+=1;d[v]+=1
 return all(d[u]!=d[v] for u,v in ee)
rows=[]
for attachment in (0,1):
 for removed in [None,*range(5)]:
  kept=[uv for j,uv in enumerate(edges[:5]) if j!=removed];d=[0]*4
  for u,v in kept:d[u]+=1;d[v]+=1
  d[2]+=attachment
  bad=[uv for uv in kept if d[uv[0]]==d[uv[1]]]
  assert bad
  rows.append({'attachment':attachment,'removed':removed,'degrees':d,'conflicts':bad})
local={}
for D in range(4):
 costs=[100,100]
 for mask in range(256):
  kept=[uv for j,uv in enumerate(edges) if mask>>j&1];d=[0]*7
  for u,v in kept:d[u]+=1;d[v]+=1
  d[6]=D
  if all(d[u]!=d[v] for u,v in kept):costs[mask>>7&1]=min(costs[mask>>7&1],8-len(kept))
 local[D]=costs
ans=[]
for t in range(1,201):
 score=min((t-D)*local[min(D,3)][0]+D*local[min(D,3)][1] for D in range(t+1))
 ans.append([t,score]);assert t==1 or score==3*t
# Literal 13-vertex graph, independent full subset enumeration.
ee=[]
for i in range(2):
 mp=lambda v: 12 if v==6 else i*6+v
 ee.extend((mp(u),mp(v)) for u,v in edges)
best=16;count=0
for mask in range(1<<16):
 k=16-mask.bit_count()
 if k>best:continue
 if valid(13,[uv for j,uv in enumerate(ee) if mask>>j&1]):
  if k<best:best=k;count=0
  count+=1
assert best==6
# Literal unbounded-pattern construction checked for many different hub degrees.
for t in range(2,201):
 ee=[]
 for i in range(t):
  mp=lambda v:6*t if v==6 else 6*i+v
  ee.extend((mp(u),mp(v)) for j,(u,v) in enumerate(edges) if j not in (0,2,6))
 assert len(ee)==5*t and valid(6*t+1,ee)
out={'diamond_cases':rows,'local_costs_by_hub_degree':local,'hub_DP':ans,'literal_t2':{'n':13,'m':16,'Ie':best,'optimal_deletion_sets':count},'construction_checks':199}
(b/'independent.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k not in ('diamond_cases','hub_DP')}))
