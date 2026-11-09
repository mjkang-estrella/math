import pathlib,itertools,json,resource,os
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);import networkx as nx
D=pathlib.Path(__file__).resolve().parents[1];out=[]
def minimum_maximal(G):
 es=list(G.edges());n=len(G);d=max(dict(G.degree()).values())
 for k in range((len(es)+2*d-2)//(2*d-1),n//2+1):
  for c in itertools.combinations(es,k):
   vs=[v for e in c for v in e]
   if len(set(vs))==2*k and all(u in vs or v in vs for u,v in es):return k
for n,d in [(8,3),(8,4),(10,3)]:
 residual=[d]*n;edges=[];types={};count=0;connected=0
 def rec(v):
  global count,connected
  if v==n:
   count+=1;G=nx.Graph();G.add_nodes_from(range(n));G.add_edges_from(edges)
   if not nx.is_connected(G):return
   connected+=1;h=nx.weisfeiler_lehman_graph_hash(G)
   if any(nx.is_isomorphic(G,H) for H in types.get(h,[])):return
   types.setdefault(h,[]).append(G.copy());gamma=minimum_maximal(G);row={'id':381469,'n':n,'delta':d,'edges':edges.copy(),'gamma_e':gamma,'violates':4*d*gamma>(2*d-1)*n+2*d,'equality':4*d*gamma==(2*d-1)*n+2*d};out.append(row);print(json.dumps(row),flush=True);(D/'outputs/regular-graphs.json').write_text(json.dumps(out,indent=2));return
  candidates=[j for j in range(v+1,n) if residual[j]>0]
  choices=[tuple(range(1,d+1))] if v==0 else itertools.combinations(candidates,residual[v])
  r=residual[v]
  for ns in choices:
   if len(ns)!=r or any(residual[j]<=0 for j in ns):continue
   residual[v]=0
   for j in ns:residual[j]-=1;edges.append((v,j))
   if all(residual[j]<=sum(residual[k]>0 for k in range(v+1,n) if k!=j) for j in range(v+1,n)):rec(v+1)
   for j in ns:residual[j]+=1;edges.pop()
   residual[v]=r
 rec(0);print(json.dumps({'space':'all labeled d-regular n-vertex graphs after fixing neighbors of vertex0 to1..d, covers every isomorphism class','n':n,'d':d,'labeled':count,'connected':connected,'isomorphism_types':sum(map(len,types.values()))}),flush=True)
