import sys;sys.path.insert(0,'/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/fresh-corpus-r10/pydeps')
import networkx as nx,itertools,json,pathlib
L=pathlib.Path(__file__).resolve().parents[1]
def partitions(n):
 a=[0]*n
 def rec(i,m):
  if i==n:yield tuple(a),m+1;return
  for j in range(m+2):a[i]=j;yield from rec(i+1,max(m,j))
 yield from rec(1,0)
ps={n:list(partitions(n)) for n in range(2,8)};out=[]
for G in nx.graph_atlas_g():
 n=len(G)
 if n<2 or not nx.is_connected(G) or not nx.check_planarity(G)[0]:continue
 edges=list(G.edges()); non=list(nx.non_edges(G));y=-100;chi=n
 for p,k in ps[n]:
  y=max(y,2*k-sum(p[u]!=p[v] for u,v in edges)-1)
  if k<chi and all(p[u]!=p[v] for u,v in non):chi=k
 lam=2 if not list(nx.bridges(G)) else 1
 if n==3 and len(edges)==3:continue
 r=dict(n=n,m=len(edges),y=y,complement_chromatic=chi,edge_connectivity_lower=lam,bound=2*chi-lam+1,violation=y>2*chi-lam+1)
 if r['violation']:r['edges']=edges
 out.append(r)
(L/'outputs/partial-dual-atlas.json').write_text(json.dumps(out,indent=2));print('graphs',len(out),'violations',sum(r['violation'] for r in out));print('by_order',{n:sum(r['n']==n for r in out) for n in range(2,8)})
