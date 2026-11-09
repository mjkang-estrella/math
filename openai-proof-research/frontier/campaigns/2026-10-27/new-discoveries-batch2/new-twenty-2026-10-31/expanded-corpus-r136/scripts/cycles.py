import pathlib,json,sys,itertools
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'sources/vendor/networkx-networkx-3.4.2'));import networkx as nx
# Exact t-vertex path counts, stopped at2; source Observation2.1.
def check(g,t):
 n=len(g);a=[list(g[u]) for u in range(n)]
 def count(u,v):
  ans=0
  def dfs(x,seen,left):
   nonlocal ans
   if ans>=2:return
   if left==0:
    ans+=x==v;return
   if x==v:return
   for y in a[x]:
    if not seen>>y&1:dfs(y,seen|1<<y,left-1)
  dfs(u,1<<u,t-1);return ans
 for u,v in itertools.combinations(range(n),2):
  c=count(u,v);want=0 if g.has_edge(u,v) else 1
  if c!=want:return {'failure_pair':[u,v],'capped_t_path_count':c,'required':want}
 return None
out=[]
# Generalized Petersen diagnostic, not a novel circulant-family nomination.
for p in range(5,19):
 for k in range(1,(p-1)//2+1):
  g=nx.Graph();g.add_nodes_from(range(2*p));g.add_edges_from((i,(i+1)%p) for i in range(p));g.add_edges_from((i,p+i) for i in range(p));g.add_edges_from((p+i,p+(i+k)%p) for i in range(p))
  for t in [10,11,12]:
   if t>2*p:continue
   fail=check(g,t);r={'family':'GP','p':p,'k':k,'t':t,'order':2*p,'first_failure':fail};out.append(r)
   if fail is None:print('CANDIDATE',r,flush=True)
 print('completed p',p,flush=True)
(D/'outputs/cycles.json').write_text(json.dumps(out,indent=2)+'\n');print('instances',len(out),'survivors',sum(x['first_failure'] is None for x in out),flush=True)
