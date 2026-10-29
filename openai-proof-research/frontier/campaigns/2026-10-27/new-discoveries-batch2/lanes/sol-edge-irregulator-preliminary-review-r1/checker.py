import json,datetime,collections
from pathlib import Path
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
D=[(0,1),(0,2),(0,3),(1,2),(1,3)]
# Six internal vertices a,b,c,d,x,y; boundary hub index 6.
E=D+[(2,4),(4,5),(5,6)]
def deg(n,es):
 d=[0]*n
 for u,v in es:d[u]+=1;d[v]+=1
 return d
def good(n,es):
 d=deg(n,es)
 return all(d[u]!=d[v] for u,v in es)
boundary=[]
for eps in (0,1):
 for mask in range(32):
  es=[e for j,e in enumerate(D) if mask>>j&1]
  d=deg(4,es);d[2]+=eps
  ok=all(d[u]!=d[v] for u,v in es)
  if ok:assert 5-len(es)>=2
  boundary.append({'epsilon':eps,'mask':mask,'degrees':d,'valid':ok})
out['diamond_boundary_64']=boundary
# Stronger falsifier: all internal constraints only, NO hub constraint.
local=[]
for mask in range(256):
 es=[e for j,e in enumerate(E) if mask>>j&1];d=deg(7,es)
 ok=all(d[u]!=d[v] for u,v in es if v!=6)
 if ok:local.append((8-len(es),mask))
assert min(x[0] for x in local)==3
out['hub_constraint_relaxed']={'valid_states':len(local),'minimum_deletions':3,'minimizers':[m for k,m in local if k==3]}
def graph(t):
 es=[]
 for i in range(t):
  es += [(6*i+u,6*i+v if v<6 else 6*t) for u,v in E]
 return 6*t+1,es
n,es=graph(2);hist=collections.Counter();best=100;mins=[]
for mask in range(1<<len(es)):
 kept=[e for j,e in enumerate(es) if mask>>j&1]
 if good(n,kept):
  cost=len(es)-len(kept);hist[cost]+=1
  if cost<best:best=cost;mins=[mask]
  elif cost==best:mins.append(mask)
assert best==6 and len(mins)==28
out['t2_exhaustive']={'masks':65536,'minimum':best,'minimizer_count':len(mins),'histogram':dict(hist),'minimizers':mins}
for t in range(2,201):
 n,es=graph(t);assert len(set(es))==len(es)==8*t and n==6*t+1
 seen={0}
 while True:
  expanded=seen|{v for u,v in es if u in seen}|{u for u,v in es if v in seen}
  if expanded==seen:break
  seen=expanded
 assert len(seen)==n
 kept=[e for j,e in enumerate(es) if j%8 not in (0,2,6)]
 assert good(n,kept) and len(es)-len(kept)==3*t
 assert deg(n,kept)==[1,2,3,1,1,1]*t+[t]
out['literal_family']={'t_min':2,'t_max':200,'count':199,'simple_connected_cardinalities_and_final_degrees':'PASS'}
Path(__file__).with_name('checker-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='diamond_boundary_64'}))
