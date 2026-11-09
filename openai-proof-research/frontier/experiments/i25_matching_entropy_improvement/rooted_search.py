import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json
from pathlib import Path
import numpy as np
import networkx as nx
from scipy.special import xlogy
from scipy.optimize import minimize
from search import matrix,evaluate
rng=np.random.default_rng(250912);records=[];top=[]
for n in [4,6,8,10,12,14]:
 for d in range(3,min(n,7)):
  for seed in range(8):
   g=nx.random_regular_graph(d,n,seed=925+n*1000+d*10+seed);ed=list(g.edges());ms,A=matrix(n,ed)
   if not ms:continue
   roots=[0] if seed>1 else range(n)
   for v in roots:
    outside=np.array([v not in e for e in ed],dtype=float)
    def fun(t,full=False):
     _,H,F,B,x,p=evaluate(A,t);W=-np.sum(outside*xlogy(1-x,1-x));R=(F-H)/max(W,1e-12)
     xx=np.clip(x,1e-12,1-1e-12);gg=-np.log(xx)-1+t-R*outside*(np.log1p(-xx)+1);ag=A@gg;grad=A.T@(p*(ag-p@ag))/max(W,1e-12)
     return (R,H,F,W,x) if full else (-R,-grad)
    for j in range(2):
     t0=np.zeros(len(ed)) if j==0 else rng.normal(0,2,len(ed))
     rr=minimize(fun,t0,jac=True,method='L-BFGS-B',bounds=[(-15,15)]*len(ed),options={'maxiter':160,'ftol':1e-12})
     R,H,F,W,x=fun(rr.x,True);r=dict(n=n,d=d,seed=seed,v=v,trial=j,N=len(ms),rooted_ratio=float(R),H=float(H),F=float(F),W=float(W));records.append(r);top.append((R,dict(r,edges=ed,theta=rr.x.tolist(),x=x.tolist())))
 print(n,len(records),max(a[0] for a in top),flush=True)
top.sort(key=lambda a:-a[0]);Path(__file__).with_name('rooted-results.json').write_text(json.dumps(dict(seed=250912,records=records,top=[a for _,a in top[:8]],limitations='Float64 local optimization; no theorem and not a counterexample certificate.'),indent=2)+'\n')
