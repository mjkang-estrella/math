import sys,pathlib;sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[1]/'vendor'))
import networkx as nx,itertools,json,time
D=pathlib.Path(__file__).resolve().parents[1];out=[];start=time.monotonic()
for G in nx.graph_atlas_g():
 n=len(G)
 if not n or n>7:continue
 found=None;orders=0
 for order in itertools.permutations(range(n)):
  rank={v:i for i,v in enumerate(order)};outs={u:[v for v in G[u] if rank[u]<rank[v]] for u in G};seq=sorted(G,key=lambda u:-len(outs[u]));used=[set() for _ in G];w=[]
  def rec(t):
   if t==n:return True
   u=seq[t];V=outs[u]
   for cols in itertools.permutations(range(len(V))):
    if any(c in used[v] for v,c in zip(V,cols)):continue
    for v,c in zip(V,cols):used[v].add(c);w.append((u,v,c))
    if rec(t+1):return True
    for v,c in zip(V,cols):used[v].remove(c);w.pop()
   return False
  orders+=1
  if rec(0):found=w;break
 out.append({'g6':nx.to_graph6_bytes(G,header=False).decode().strip(),'n':n,'orders':orders,'acyclic_witness':found})
 if found is None:print('NO ACYCLIC WITNESS',out[-1],flush=True)
 if time.monotonic()-start>100:print('STOP',len(out),flush=True);break
(D/'outputs/sequential.json').write_text(json.dumps(out)+'\n');print('graphs',len(out),'witnesses',sum(r['acyclic_witness'] is not None for r in out),'seconds',time.monotonic()-start)
