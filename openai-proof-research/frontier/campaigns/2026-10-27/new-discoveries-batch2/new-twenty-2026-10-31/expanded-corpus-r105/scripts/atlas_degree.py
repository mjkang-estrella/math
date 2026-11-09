import sys,pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1];V=D.parent/'fresh-corpus-r13/vendor';sys.path.insert(0,str(V));import networkx as nx
out=[]
for n in [5,6,7]:
 graphs=[g for g in nx.graph_atlas_g() if len(g)==n and nx.is_connected(g)];rec=dict(n=n,connected=len(graphs),classes={})
 for kind in ['vertex','edge']:
  conn=nx.node_connectivity if kind=='vertex' else nx.edge_connectivity;best=-1;wins=[];ct=0;k=2 if n<7 else 3
  if n<2*k+1:continue
  for g in graphs:
   if min(dict(g.degree()).values())<k or conn(g)!=k:continue
   minimal=True
   for u,v in list(g.edges()):
    g.remove_edge(u,v);z=conn(g);g.add_edge(u,v)
    if z>=k:minimal=False;break
   if not minimal:continue
   ct+=1;total=sum(conn(g,s=u,t=v) for u in range(n) for v in range(u+1,n)) if kind=='vertex' else sum(nx.edge_connectivity(g,u,v) for u in range(n) for v in range(u+1,n))
   if total>best:best=total;wins=[]
   if total==best:wins.append(dict(edges=list(g.edges()),degree_partitioned=all((g.degree(u)==k)!=(g.degree(v)==k) for u,v in g.edges())))
  rec['classes'][kind]=dict(k=k,minimal_graphs=ct,max_total_local_connectivity=best,optimizers=wins)
 out.append(rec);print(rec,flush=True);(D/'outputs/atlas-degree.json').write_text(json.dumps(out,indent=2))
