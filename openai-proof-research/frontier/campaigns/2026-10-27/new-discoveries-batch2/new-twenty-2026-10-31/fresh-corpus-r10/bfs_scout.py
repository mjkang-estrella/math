import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import networkx as nx,numpy as np,json,time,random
from pathlib import Path
w=Path(__file__).parent
random.seed(330880);start=time.time();tested=0;best=0
for n in range(8,17):
 groups={}
 for g in nx.nonisomorphic_trees(n):
  deg=tuple(sorted(dict(g.degree()).values(),reverse=True))
  if deg not in groups:
   h=nx.Graph();h.add_nodes_from(range(n));cur=1
   for v,d in enumerate(deg):
    for _ in range(d-(v!=0)):
     if cur<n:h.add_edge(v,cur);cur+=1
   dh=np.array(nx.floyd_warshall_numpy(h)); leaf=[v for v in h if h.degree(v)==1]
   groups[deg]=(h,np.linalg.eigvalsh(dh)[-1],np.linalg.eigvalsh(dh[np.ix_(leaf,leaf)])[-1])
  h,r,s=groups[deg];dg=np.array(nx.floyd_warshall_numpy(g,nodelist=list(range(n))));leaf=[v for v in g if g.degree(v)==1]
  for typ,target,val in [('distance',r,np.linalg.eigvalsh(dg)[-1]),('terminal',s,np.linalg.eigvalsh(dg[np.ix_(leaf,leaf)])[-1])]:
   tested+=1
   if target-val>1e-7:
    out=dict(n=n,kind=typ,g=list(g.edges()),bfs=list(h.edges()),rho_g=float(val),rho_bfs=float(target),diagnostic_only=True)
    (w/'bfs_candidate.json').write_text(json.dumps(out,indent=2));print(out,flush=True);raise SystemExit
 print(dict(n=n,tested=tested,elapsed=time.time()-start),flush=True)
 if time.time()-start>120:break
(w/'bfs_scout.json').write_text(json.dumps(dict(tested=tested,elapsed=time.time()-start,no_numeric_violation=True)))
