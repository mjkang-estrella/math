from pathlib import Path
import itertools,json
import networkx as nx
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
import numpy as np
P=Path(__file__).resolve().parent
# x_v=1 iff outside; y_uv=1 iff v is chosen private neighbour of u.
def solve(g,cutoff):
 g=nx.convert_node_labels_to_integers(g);n=len(g);arcs=list(g.edges())+[(v,u) for u,v in g.edges()];ix={a:n+i for i,a in enumerate(arcs)};rows=[];lo=[];hi=[]
 def row(d,l=-np.inf,h=np.inf):rows.append(d);lo.append(l);hi.append(h)
 for u in g:
  d={u:-1};d.update({ix[u,v]:1 for v in g[u]});row(d,0,np.inf)
 for (u,v),i in ix.items():
  row({i:1,u:-1},h=0);row({i:1,v:1},h=1)
  for w in g[v]:
   if w!=u:row({i:1,w:1},h=1)
 row({i:1 for i in range(n)},n-cutoff+1,np.inf)
 a=lil_matrix((len(rows),n+len(arcs)))
 for i,d in enumerate(rows):
  for j,v in d.items():a[i,j]=v
 r=milp(np.zeros(n+len(arcs)),integrality=np.ones(n+len(arcs)),bounds=Bounds(0,1),constraints=LinearConstraint(a.tocsr(),lo,hi),options={'time_limit':4,'mip_rel_gap':0})
 if r.x is None:return {'status':int(r.status)}
 out=[i for i in range(n) if r.x[i]>.5];S=set(g)-set(out)
 assert all(any(set(g[v])&set(out)=={u} for v in S) for u in out)
 return dict(status=int(r.status),outside=out,size=n-len(out),edges=list(g.edges()))
def gamma(g):
 n=len(g);adj=[sum(1<<v for v in g[u]) for u in g];allmask=(1<<n)-1
 for k in range((n+1)//2,n+1):
  for S in itertools.combinations(range(n),k):
   s=sum(1<<v for v in S);o=allmask^s
   if all(any(adj[v]&o==1<<u for v in S) for u in range(n) if o>>u&1):return k
atlas=[g for g in nx.graph_atlas_g() if 3<=len(g)<=6 and nx.is_connected(g)]
# retain factors with large normalized gamma, and varied structure
factors=[]
for g in atlas:
 z=gamma(g)
 if z*4>=3*len(g):factors.append((g,z))
factors=factors[:45]
print('factors',len(factors),flush=True);results=[]
for i,(g,a) in enumerate(factors):
 for j,(h,b) in enumerate(factors[i:],i):
  if a*b<=(len(g)*len(h)+1)//2:continue
  r=solve(nx.cartesian_product(g,h),a*b);r.update(i=i,j=j,n=len(g),m=len(h),rhs=a*b);results.append(r)
  if 'outside' in r:
   print('COUNTEREXAMPLE',i,j,r['size'],a*b,flush=True);(P/'counterexample.json').write_text(json.dumps(dict(g=list(g.edges()),h=list(h.edges()),a=a,b=b,result=r),indent=2));break
 else:continue
 break
(P/'search-results.json').write_text(json.dumps(results,indent=2));print('pairs',len(results),'statuses',{s:sum(x['status']==s for x in results) for s in {x['status'] for x in results}},flush=True)
