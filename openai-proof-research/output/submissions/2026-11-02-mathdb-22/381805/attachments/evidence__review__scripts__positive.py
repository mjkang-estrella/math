import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='2'
import numpy as np,scipy.optimize as so,scipy.sparse as sp,json,pathlib,warnings
r=pathlib.Path(__file__).resolve().parents[1];out=[]
for n,last in [(5,8),(7,5),(7,8),(7,15),(9,10),(9,20)]:
 ks=[1]*(n-1)+[last];p=n+sum(ks);edges=[(i,(i+1)%n) for i in range(n)];j=n
 for i,k in enumerate(ks):
  for _ in range(k):edges.append((i,j));j+=1
 rows=[];cols=[];vals=[];lo=[];hi=[];S=2*p*p
 def row(ts,l,h):
  idx=len(lo)
  for c,v in ts:rows.append(idx);cols.append(c);vals.append(v)
  lo.append(l);hi.append(h)
 for v in range(p):row([(v*p+l,1) for l in range(p)],1,1)
 for l in range(p):row([(v*p+l,1) for v in range(p)],1,1)
 for e in range(p):row([(p*p+e*p+l,1) for l in range(p)],1,1)
 for l in range(p):row([(p*p+e*p+l,1) for e in range(p)],1,1)
 for e,(u,v) in enumerate(edges):row([(u*p+l,l+1) for l in range(p)]+[(v*p+l,l+1) for l in range(p)]+[(p*p+e*p+l,-l) for l in range(p)]+[(S,-1)],0,0)
 # Break permutation symmetry within each leaf fiber.
 for i in range(n,p-1):
  if edges[i][0]==edges[i+1][0]:row([(i*p+l,l+1) for l in range(p)]+[((i+1)*p+l,-l-1) for l in range(p)],-np.inf,-1)
 lb=np.zeros(S+1);ub=np.ones(S+1);lb[S]=3;ub[S]=(n+1)//2
 with warnings.catch_warnings():
  warnings.simplefilter('ignore');res=so.milp(np.zeros(S+1),integrality=np.ones(S+1),bounds=so.Bounds(lb,ub),constraints=so.LinearConstraint(sp.csc_matrix((vals,(rows,cols)),shape=(len(lo),S+1)),lo,hi),options={'time_limit':12,'threads':2})
 o=dict(n=n,ks=ks,status=int(res.status),message=res.message,time_limit=12)
 if res.x is not None:
  lab=[int(np.argmax(res.x[v*p:(v+1)*p]))+1 for v in range(p)];sums=sorted(lab[u]+lab[v] for u,v in edges);o.update(labels=lab,sums=sums,exact_verified=sorted(lab)==list(range(1,p+1)) and sums==list(range(sums[0],sums[0]+p)),counterexample=sums[0]<(n+3)//2)
 out.append(o);(r/'logs/positive.json').write_text(json.dumps(out,indent=2));print(o,flush=True)
