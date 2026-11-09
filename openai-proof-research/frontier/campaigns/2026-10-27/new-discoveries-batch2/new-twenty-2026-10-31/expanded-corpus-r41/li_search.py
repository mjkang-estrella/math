import os,resource,pathlib,json
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1');resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(45,45));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
import numpy as np,networkx as nx
p=pathlib.Path(__file__).resolve().parent;out=[];tested=0
for g in nx.graph_atlas_g():
 n=len(g);m=g.number_of_edges()
 if n<3 or not nx.is_connected(g) or not n<=m<=2*n-3:continue
 tested+=1;t=m-n+1;h=nx.Graph();h.add_nodes_from(range(n));h.add_edge(0,1)
 for v in range(2,2+t):h.add_edge(0,v);h.add_edge(1,v)
 for v in range(2+t,n):h.add_edge(0,v)
 def norms(g):
  a=nx.to_numpy_array(g);l=np.diag(a.sum(axis=0))-a-(2*m/n)*np.eye(n);s=sorted(abs(np.linalg.eigvalsh(l)),reverse=True);return [sum(s[:2]),sum(s[:3])]
 a=norms(g);b=norms(h)
 if any(x>y+1e-7 for x,y in zip(a,b)) or (any(abs(x-y)<1e-7 for x,y in zip(a,b)) and not nx.is_isomorphic(g,h)):
  out.append({'n':n,'m':m,'edges':list(g.edges()),'target_edges':list(h.edges()),'norms':a,'target_norms':b});print(out[-1],flush=True)
(p/'li-diagnostic.json').write_text(json.dumps({'tested':tested,'potential_witnesses':out},indent=2));print('tested',tested,'flags',len(out))
