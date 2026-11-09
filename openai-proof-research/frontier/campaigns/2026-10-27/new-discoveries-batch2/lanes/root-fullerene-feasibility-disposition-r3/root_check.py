from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations
import json
d=Path(__file__).parent;a=json.loads((d/'rational-realizations.json').read_text())
def dot(x,y):return sum((u*v for u,v in zip(x,y)),Q(0))
def sub(x,y):return [u-v for u,v in zip(x,y)]
def cross(x,y):return [x[1]*y[2]-x[2]*y[1],x[2]*y[0]-x[0]*y[2],x[0]*y[1]-x[1]*y[0]]
out={}
for name,t in a.items():
 qs=[list(map(Q,v)) for v in t['dual_vertices']];ps=[list(map(Q,v)) for v in t['primal_vertices']]
 assert len(qs)==32 and len(ps)==60
 assert len(set(map(tuple,qs)))==32 and len(set(map(tuple,ps)))==60
 assert all(sum(v[j] for v in qs)==0 for j in range(3))
 faces=[set(f) for f in t['dual_facets']]
 inc=[]
 for k,p in enumerate(ps):
  vals=[dot(x,p) for x in qs]
  assert max(vals)==1 and all(v<=1 for v in vals)
  active={i for i,v in enumerate(vals) if v==1}
  assert active==faces[k] and len(active)==3
  i,j,l=sorted(active);assert dot(qs[i],cross(qs[j],qs[l]))!=0
  inc.append(active)
 for i in range(32):
  ids={j for j in range(60) if i in inc[j]}
  assert ids==set(t['primal_facets'][i]) and len(ids) in (5,6)
  base=ps[min(ids)]
  assert any(cross(sub(ps[j],base),sub(ps[k],base))!=[0,0,0] for j,k in combinations(ids,2))
 edges={tuple(sorted((i,j))) for f in faces for i,j in combinations(f,2)}
 assert len(edges)==90
 for i,j in combinations(range(32),2):
  common={k for k in range(60) if i in inc[k] and j in inc[k]}
  assert len(common)==(2 if (i,j) in edges else 0)
 assert sum(len(f)==5 for f in t['primal_facets'])==12
 out[name]={'dot_inequalities':1920,'independent_active_triples':60,'noncollinear_primal_facets':32,'facet_pair_tests':496,'edge_count':90,'status':'PASS'}
(d/'root-coordinate-check.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
