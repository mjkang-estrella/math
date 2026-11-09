import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import networkx as nx,numpy as np,json,time
from pathlib import Path
w=Path(__file__).parent
start=time.time(); report=[]
def geo(g):
 n=len(g); states=[frozenset()]+[frozenset([v]) for v in g]+[frozenset(e) for e in g.edges()]; idx={s:i for i,s in enumerate(states)}; trans=[]
 for s in states:
  trans.append([idx[frozenset([v])|(s&frozenset(g[v]))] for v in g if v not in s])
 a=[1]+[0]*(len(states)-1); ans=[]
 for k in range(2*n):
  b=[0]*len(states)
  for i,t in enumerate(trans):
   for j in t:b[j]+=a[i]
  a=b;ans.append(sum(a))
 return ans
for n in range(16,20):
 groups={};coll=0
 for g in nx.nonisomorphic_trees(n):
  a=nx.to_numpy_array(g); l=np.diag(a.sum(axis=1))-a
  key=tuple(np.round(np.linalg.eigvalsh(a),7))+tuple(np.round(np.linalg.eigvalsh(l),7))+tuple(np.round(np.linalg.eigvalsh(np.ones((n,n))-np.eye(n)-a),7))
  if key in groups:
   h=groups[key];coll+=1
   x,y=geo(g),geo(h)
   if x!=y:
    out=dict(n=n,g=list(g.edges()),h=list(h.edges()),counts_g=x,counts_h=y,diagnostic_only=True)
    (w/'spectral_candidate.json').write_text(json.dumps(out,indent=2));print(out,flush=True);raise SystemExit
  else:groups[key]=g
 report.append(dict(n=n,groups=len(groups),collisions=coll,elapsed=time.time()-start));print(report[-1],flush=True)
 if time.time()-start>150:break
(w/'spectral_scout.json').write_text(json.dumps(report,indent=2))
