from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import json,hashlib
L=Path(__file__).resolve().parent
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def cross(a,b):return [a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]]
def sub(a,b):return [x-y for x,y in zip(a,b)]
results={}
data=json.loads((L/'frozen/sol-fullerene-literal-feasibility-prior-r2--rational-realizations.json').read_text())
for name,c in data.items():
 q=[[F(x) for x in v] for v in c['dual_vertices']];p=[[F(x) for x in v] for v in c['primal_vertices']]
 assert len(q)==32 and len(p)==60 and len(set(map(tuple,p)))==60
 assert all(sum(v[k] for v in q)==0 for k in range(3))
 triple_points=set();singular=0;feasible=[]
 for tri in combinations(range(32),3):
  a,b,d=[q[i] for i in tri];det=dot(a,cross(b,d))
  if not det:singular+=1;continue
  bc,ca,ab=cross(b,d),cross(d,a),cross(a,b)
  v=tuple((bc[k]+ca[k]+ab[k])/det for k in range(3))
  if all(dot(u,v)<=1 for u in q):triple_points.add(v);feasible.append(tri)
 assert triple_points==set(map(tuple,p))
 inc=[[j for j,v in enumerate(p) if dot(u,v)==1] for u in q]
 assert inc==c['primal_facets']
 assert all(dot(u,v)<=1 for u in q for v in p)
 for j,v in enumerate(p):
  active=[i for i,u in enumerate(q) if dot(u,v)==1]
  assert set(active)==set(c['dual_facets'][j]) and len(active)==3
  assert dot(q[active[0]],cross(q[active[1]],q[active[2]]))
 for ids in inc:
  assert any(any(cross(sub(p[j],p[ids[0]]),sub(p[k],p[ids[0]]))) for j,k in combinations(ids[1:],2))
 edges={tuple(e) for e in json.loads((L/f'frozen/sol-fullerene-heat-trace-breadth-depth-r286--{name}-edges.json').read_text())}
 actual={(i,j) for i,j in combinations(range(32),2) if len(set(inc[i])&set(inc[j]))==2}
 assert {tuple(sorted(e)) for e in edges}==actual
 pe={tuple(sorted(set(inc[i])&set(inc[j]))) for i,j in actual}
 assert len(pe)==90 and all(sum(v in e for e in pe)==3 for v in range(60))
 assert sorted(map(len,inc))==[5]*12+[6]*20
 for ids in inc:
  es=[e for e in pe if set(e)<=set(ids)]
  assert len(es)==len(ids) and all(sum(i in e for e in es)==2 for i in ids)
  seen={ids[0]}
  for _ in ids:seen|={v for e in es if set(e)&seen for v in e}
  assert seen==set(ids)
 weights=json.loads((L/f'positive-span-{name}.json').read_text())
 for k,pair in enumerate(weights):
  for sign,cs in zip([1,-1],pair):
   cs=list(map(F,cs));assert min(cs)>=0
   assert [sum(cs[i]*q[i][j] for i in range(32)) for j in range(3)]==[F(sign if j==k else 0) for j in range(3)]
 results[name]=dict(triples=4960,singular=singular,feasible_triples=len(feasible),distinct_feasible_points=len(triple_points),facets_5_6=[12,20],pair_incidence_edges=len(actual),primal_edges=len(pe),scope='Exact rational evidence, not an imported Lean theorem')
(L/'coordinate-check.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results))
