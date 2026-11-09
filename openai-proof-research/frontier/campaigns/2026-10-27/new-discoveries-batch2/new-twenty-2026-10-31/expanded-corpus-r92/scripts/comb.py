import json,time
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def greedy(n,m,T,S):
 a=[max(0,m-max(0,T-1-abs(x-S))-1) for x in range(n)]
 if T<n:return False
 for r in range(T-2,-1,-1):
  j=max(range(n),key=lambda i:a[i]);a[j]=max(0,a[j]-2*r-1)
 return max(a)==0
out=[]
for n in range(2,9):
 for m in range(n,41):
  g=next(T for T in range(n,n*m+1) if any(greedy(n,m,T,S) for S in range(n)))
  T=g-1
  if T<n:out.append(dict(n=n,m=m,greedy=g,lower_bound=n));continue
  V=[(x,y) for x in range(n) for y in range(m)];N=len(V)
  dist=np.array([[abs(x-a)+y+b if x!=a else abs(y-b) for a,b in V] for x,y in V])
  cover=np.concatenate([dist<=r for r in range(T)],axis=1)
  slots=np.kron(np.eye(T),np.ones((1,N)))
  A=np.concatenate([cover,slots]);lo=np.r_[np.ones(N),np.zeros(T)];hi=np.r_[np.full(N,np.inf),np.ones(T)]
  r=milp(np.zeros(T*N),integrality=np.ones(T*N),bounds=Bounds(0,1),constraints=LinearConstraint(A,lo,hi),options={'time_limit':1,'threads':1})
  row=dict(n=n,m=m,greedy=g,T=T,status=int(r.status),message=r.message)
  if r.x is not None:
   chosen=[(radius,V[v]) for radius in range(T) for v in range(N) if r.x[radius*N+v]>.5]
   if all(any(dist[v,V.index(c)]<=rad for rad,c in chosen) for v in range(N)):
    row['counterexample_centers']=chosen;out.append(row);print(row,flush=True);break
  out.append(row)
 else:continue
 break
(D/'outputs/comb.json').write_text(json.dumps(out,indent=2));print('completed',len(out),flush=True)
