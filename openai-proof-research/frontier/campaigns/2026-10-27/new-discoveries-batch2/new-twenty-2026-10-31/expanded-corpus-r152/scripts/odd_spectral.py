import sys;sys.path.insert(0,'/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/fresh-corpus-r10/pydeps')
import networkx as nx,json,pathlib,math
L=pathlib.Path(__file__).resolve().parents[1]
def rho(G):
 n=len(G);x=[1/math.sqrt(n)]*n;adj=[list(G.neighbors(i)) for i in range(n)]
 for _ in range(1500):
  y=[n*x[i]+sum(x[j] for j in adj[i]) for i in range(n)];norm=math.sqrt(sum(v*v for v in y));y=[v/norm for v in y]
  if max(abs(a-b) for a,b in zip(x,y))<1e-13:x=y;break
  x=y
 return sum(x[i]*sum(x[j] for j in adj[i]) for i in range(n))
out=[]
for G in nx.graph_atlas_g():
 n=len(G);m=G.number_of_edges()
 if n<3 or not nx.is_connected(G) or nx.is_bipartite(G) or m%2==0:continue
 for k in range(1,3):
  # exclude all short odd cycles via simple DFS
  def cyc(v,start,path):
   if len(path)>2*k+1:return False
   for w in G[v]:
    if w==start and len(path)>=3 and len(path)%2:return True
    if w not in path and cyc(w,start,path+[w]):return True
   return False
  if any(cyc(v,v,[v]) for v in G):continue
  t=(m-2*k+1)//2
  if t<2:continue
  H=nx.complete_bipartite_graph(2,t);H.remove_edge(0,2);prev=0
  for i in range(2*k-1):w=len(H);H.add_edge(prev,w);prev=w
  H.add_edge(prev,2);diff=rho(G)-rho(H);out.append(dict(n=n,m=m,k=k,difference=diff,violation=diff>1e-8))
(L/'outputs/odd-spectral.json').write_text(json.dumps(out,indent=2));print('cases',len(out),'violations',sum(r['violation'] for r in out));print(json.dumps(out))
