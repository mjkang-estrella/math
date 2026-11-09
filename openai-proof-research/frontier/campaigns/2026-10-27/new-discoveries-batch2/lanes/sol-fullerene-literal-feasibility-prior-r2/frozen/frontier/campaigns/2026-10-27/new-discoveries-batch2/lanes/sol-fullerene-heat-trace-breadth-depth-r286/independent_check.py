from pathlib import Path
from fractions import Fraction as F
import json,math
L=Path(__file__).resolve().parent
def connected(adj,removed=()):
 todo=[v for v in adj if v not in removed];seen=set();stack=todo[:1]
 while stack:
  v=stack.pop()
  if v in seen:continue
  seen.add(v);stack.extend(w for w in adj[v] if w not in seen and w not in removed)
 return len(seen)==len(todo)
cert=json.loads((L/'graph-certificates.json').read_text());graphs=[]
for name in ['G','H']:
 edges=json.loads((L/(name+'-edges.json')).read_text());assert len(edges)==90
 adj={v:set() for v in range(32)}
 for u,v in edges:assert u!=v and v not in adj[u];adj[u].add(v);adj[v].add(u)
 assert sorted(map(len,adj.values()))==[5]*12+[6]*20
 assert all(connected(adj,(u,v)) for u in adj for v in range(u,32))
 rot={int(v):a for v,a in cert[name]['rotation'].items()}
 assert all(set(rot[v])==adj[v] and len(rot[v])==len(adj[v]) for v in adj)
 darts={(u,v) for u in adj for v in adj[u]};faces=[]
 while darts:
  start=min(darts);cur=start;face=[]
  while not face or cur!=start:
   assert cur in darts;darts.remove(cur);u,v=cur;face.append(u);r=rot[v];cur=(v,r[(r.index(u)-1)%len(r)])
  assert len(face)==3;faces.append(face)
 assert len(faces)==60 and 32-90+len(faces)==2
 # Rotation system gives a connected orientable cellular sphere embedding.
 incidence={tuple(sorted(e)):[] for e in edges}
 for i,face in enumerate(faces):
  for k in range(3):incidence[tuple(sorted((face[k],face[(k+1)%3])))].append(i)
 assert all(len(f)==2 and f[0]!=f[1] for f in incidence.values())
 dual={i:set() for i in range(60)}
 for i,j in incidence.values():assert j not in dual[i];dual[i].add(j);dual[j].add(i)
 assert connected(dual) and all(len(s)==3 for s in dual.values())
 assert all(connected(dual,(u,v)) for u in dual for v in range(u,60))
 graphs.append(adj)
def series(adj,a,b):
 q=math.lcm(a.denominator,b.denominator);aa=int(a*q);bb=int(b*q)
 M=[[(j,aa) for j in adj[i]]+[(i,bb*len(adj[i]))] for i in range(32)]
 P=[[int(i==j) for j in range(32)] for i in range(32)];S=F(32);den=1;tr=[]
 for k in range(1,91):
  N=[[0]*32 for _ in range(32)]
  for i in range(32):
   for j in range(32):
    c=P[i][j]
    for v,w in M[j]:N[i][v]+=c*w
  P=N;den*=q*k;t=sum(P[i][i] for i in range(32));tr.append(t);S+=F(t,den)
 R=F(6*(aa+bb),q);E=32*3**math.ceil(R)*R**91/math.factorial(91)
 return S,E,tr
checks=[]
for r in json.loads((L/'exact-signs.json').read_text()):
 a,b=F(r['alpha']),F(r['beta']);x,ex,tx=series(graphs[0],a,b);y,ey,ty=series(graphs[1],a,b)
 lo=x-y-ey;hi=x-y+ex;assert lo==F(r['lower']) and hi==F(r['upper'])
 if b==F(1,50):assert F(1,1000)<lo<hi<F(1,500)
 else:assert -2<lo<hi<-1
 assert tx[5]!=ty[5]
 checks.append(dict(alpha=str(a),beta=str(b),exact_interval_reproduced=True,first_distinct_moment=6))
print(json.dumps(dict(status='PASS',libraries='stdlib only, independent sparse multiplication and rotation-system traversal',graphs='32 vertices, 90 edges, 60 triangular faces; both primal and dual 3-connected',checks=checks)))
