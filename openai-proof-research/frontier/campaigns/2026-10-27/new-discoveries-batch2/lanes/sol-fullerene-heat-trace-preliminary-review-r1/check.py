"""Solo reconstruction; no worker/root code imported. Exact integer arithmetic."""
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter,defaultdict
from itertools import combinations
from math import factorial,ceil
import json,re,hashlib
L=Path(__file__).resolve().parent;F=L/'frozen'
def verify_frozen():
 for r in json.loads((L/'freeze.json').read_text()):
  assert hashlib.sha256(Path(r['original']).read_bytes()).hexdigest()==r['sha256']
  assert hashlib.sha256((L/r['copy']).read_bytes()).hexdigest()==r['sha256']
verify_frozen()
cert=json.loads((F/'graph-certificates.json').read_text());proof=(F/'PROOF.md').read_text()
def connected(adj,removed):
 left=set(range(len(adj)))-set(removed);seen={next(iter(left))};todo=list(seen)
 while todo:
  v=todo.pop()
  for u in adj[v]&left-seen:seen.add(u);todo.append(u)
 return seen==left
def cuts(adj):
 n=len(adj);count=0
 for k in range(3):
  for s in combinations(range(n),k):assert connected(adj,s);count+=1
 return count
graphs=[];out={}
for col,name in enumerate(['G','H'],2):
 edges=json.loads((F/(name+'-edges.json')).read_text());es={tuple(sorted(e)) for e in edges}
 assert len(es)==90==len(edges) and all(0<=a<b<32 for a,b in es)
 adj=[set() for _ in range(32)]
 for a,b in es:adj[a].add(b);adj[b].add(a)
 for row in proof.splitlines():
  if row.startswith('| ') and row.split('|')[1].strip().isdigit():
   cells=row.split('|');v=int(cells[1]);ns=set(map(int,cells[col].strip().split(',')))
   assert adj[v]==ns
 faces=cert[name]['faces'];assert len(faces)==60
 darts={};links=[[] for _ in range(32)]
 for fi,t in enumerate(faces):
  assert len(t)==len(set(t))==3
  for i,v in enumerate(t):
   a,b=t[(i+1)%3],t[(i+2)%3]
   assert tuple(sorted((v,a))) in es and (v,a) not in darts
   darts[v,a]=fi;links[v].append((a,b))
 assert len(darts)==180 and all((b,a) in darts for a,b in darts)
 for v,arcs in enumerate(links):
  nxt=dict(arcs);assert len(nxt)==len(arcs)==len(adj[v]) and set(nxt)==set(nxt.values())==adj[v]
  s=next(iter(nxt));walk=[];u=s
  while u not in walk:walk.append(u);u=nxt[u]
  assert u==s and len(walk)==len(adj[v])
  rot=cert[name]['rotation'][str(v)]
  assert len(rot)==len(adj[v]) and set(rot)==adj[v]
  # The oriented face (v,a,b) gives successor a -> b in the stored rotation.
  assert all(nxt[rot[i]]==rot[(i+1)%len(rot)] for i in range(len(rot)))
 dual=[set() for _ in faces]
 for (a,b),i in darts.items():
  j=darts[b,a];assert i!=j;dual[i].add(j)
 assert all(len(a)==3 for a in dual)
 assert 32-90+60==2
 # Primal vertex stars are the dual facial boundaries; adjacency closes every cycle.
 for v in range(32):
  ns=list(adj[v]);star={darts[v,u] for u in ns}
  assert len(star)==len(adj[v])
  assert all(len(dual[i]&star)==2 for i in star)
 deg=Counter(map(len,adj));assert deg=={5:12,6:20}
 out[name]={'V':32,'E':90,'oriented_triangles':60,'euler':2,'vertex_links':'single circles','dual_order':60,'dual_face_sizes':dict(deg),'primal_deletion_tests':cuts(adj),'dual_deletion_tests':cuts(dual)}
 graphs.append(adj)
def traces(adj,a,d,K):
 n=len(adj);P=[[int(i==j) for j in range(n)] for i in range(n)];t=[n]
 for k in range(K):
  P=[[d*len(adj[i])*P[i][j]+a*sum(P[u][j] for u in adj[i]) for j in range(n)] for i in range(n)]
  t.append(sum(P[i][i] for i in range(n)))
 return t
signs=[]
for a,d,q in [(45,1,50),(9,9,10)]:
 ts=[traces(g,a,d,90) for g in graphs]
 S=sum((Q(x-y,q**k*factorial(k)) for k,(x,y) in enumerate(zip(*ts))),Q(0))
 R=Q(6*(a+d),q);E=32*3**ceil(R)*R**91/factorial(91)
 lo,hi=S-E,S+E
 if d==1:assert Q(1,1000)<lo<hi<Q(1,500)
 else:assert -2<lo<hi<-1
 signs.append({'alpha':'9/10','beta':str(Q(d,q)),'R':str(R),'K':90,'tail_per_graph':str(E),'lower':str(lo),'upper':str(hi),'sixth_moments':[t[6] for t in ts]})
assert signs[0]['sixth_moments']==[540051518791920,540051567999420]
out['signs']=signs;out['nonisomorphic']=True
out['adjacency_moments_0_to_10']=[traces(g,1,0,10) for g in graphs]
assert out['adjacency_moments_0_to_10'][0]!=out['adjacency_moments_0_to_10'][1]
verify_frozen();(L/'independent-evidence.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'PASS':True,'graph_tests':{x:out[x] for x in ['G','H']},'strict_signs':['1/1000 < f(1/50) < 1/500','-2 < f(9/10) < -1']}))
