import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,math,itertools
from pathlib import Path
import numpy as np
import networkx as nx
from scipy.special import logsumexp,xlogy
from scipy.optimize import minimize
from search import matrix,evaluate,optimize,expand
OUT=Path(__file__).parent
rng=np.random.default_rng(250911)
rows=[];top=[]
# Perturb low-dimensional tight-cut extremizers with added nonedges.
for depth in [4,6,8,10,12]:
 n=2;ee=[(0,1)]*3
 cuts=[]
 for k in range(depth):
  n,ee=expand(n,ee,0)
 # discover base tight face from 3-edge-colorings obtained by scalar expansion lineage
 _,A0=matrix(n,ee)
 # Find all odd cuts of triangle (all triangles suffice for this chain), penalize crossings.
 g=nx.Graph();g.add_edges_from(ee)
 tris=[set(t) for t in itertools.combinations(range(n),3) if all(g.has_edge(a,b) for a,b in itertools.combinations(t,2))]
 missing=[e for e in itertools.combinations(range(n),2) if not g.has_edge(*e)]
 for trial in range(14):
  extra=[] if trial==0 else [missing[i] for i in rng.choice(len(missing),size=min(trial,len(missing)),replace=False)]
  ed=ee+extra;ms,A=matrix(n,ed)
  if len(ms)>200000:continue
  t=np.zeros(len(ed))
  for S in tris:
   t-=4*np.array([(u in S)!=(v in S) for u,v in ed])
  t[len(ee):]-=3
  for tt in [t,optimize(A,t,180)]:
   R,H,F,B,x,p=evaluate(A,tt)
   record=dict(name=f'klee-plus-{depth}-{trial}',n=n,s=len(ed),N=len(ms),ratio=float(R),H=float(H),F=float(F),B=float(B))
   rows.append(record);top.append((R,dict(record,edges=ed,theta=tt.tolist(),x=x.tolist())))
 print('depth',depth,'laws',len(rows),'best',max(a[0] for a in top),flush=True)
# Rooted block diagnostic for tight-cut repetition: D/(B-b_star).
blocks=[]
for n in [4,6,8,10,12,14,16]:
 for d in range(3,min(n,8)):
  for seed in range(6):
   g=nx.random_regular_graph(d,n,seed=100000+n*1000+d*100+seed);ed=list(g.edges());ms,A=matrix(n,ed)
   if not ms or len(ms)>150000:continue
   # Uniform marginal feasibility via entropy dual optimizer. Boundary failure is recorded, never treated as proof.
   target=np.full(len(ed),1/d)
   def fun(t):
    z=A@t;lz=logsumexp(z);p=np.exp(z-lz);return lz-target@t,p@A-target
   rr=minimize(fun,np.zeros(len(ed)),jac=True,method='L-BFGS-B',options={'maxiter':150,'ftol':1e-13})
   R,H,F,B,x,p=evaluate(A,rr.x);err=float(np.max(abs(x-target)))
   if err>1e-7:continue
   b=(d-1)*math.log(d/(d-1));amp=(F-H)/(B-b)
   blocks.append(dict(n=n,d=d,seed=seed,N=len(ms),uniform_error=err,H=float(H),ratio=float(R),amplified_ratio=float(amp)))
 print('blocks n',n,'best',max([a['amplified_ratio'] for a in blocks] or [0]),flush=True)
top.sort(key=lambda t:-t[0]);blocks.sort(key=lambda a:-a['amplified_ratio']);(OUT/'structured-results.json').write_text(json.dumps(dict(seed=250911,perturbation_laws=len(rows),rows=rows,top=[a for _,a in top[:10]],blocks=blocks,limitations='Floating approximate uniform means only; optimization is local; tree repetition formula exact only at exactly compatible means.'),indent=2)+'\n')
