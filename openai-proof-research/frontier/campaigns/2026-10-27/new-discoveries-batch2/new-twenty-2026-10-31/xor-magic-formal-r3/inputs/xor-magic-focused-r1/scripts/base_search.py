import sys,json,itertools
from pathlib import Path
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
N=int(sys.argv[1]);d=int(sys.argv[2]);closed=int(sys.argv[3]);sec=int(sys.argv[4]);n=N.bit_length()-1
E=list(itertools.combinations(range(N),2));m=len(E);A=lil_matrix((N*(n+1),m+N*n));rhs=np.zeros(N*(n+1));rhs[:N]=d
for i,(u,v) in enumerate(E):
 A[u,i]=A[v,i]=1
 for b in range(n):
  A[N+u*n+b,i]=(v>>b)&1;A[N+v*n+b,i]=(u>>b)&1
for u in range(N):
 for b in range(n):A[N+u*n+b,m+u*n+b]=-2;rhs[N+u*n+b]=-closed*((u>>b)&1)
r=milp(np.zeros(m+N*n),integrality=np.ones(m+N*n),bounds=Bounds(np.zeros(m+N*n),np.r_[np.ones(m),np.full(N*n,(d+closed)//2)]),constraints=LinearConstraint(A.tocsr(),rhs,rhs),options={'time_limit':sec,'mip_rel_gap':0,'disp':True})
out=dict(N=N,d=d,closed=bool(closed),status=int(r.status),message=r.message)
if r.x is not None:out['edges']=[e for i,e in enumerate(E) if r.x[i]>.5]
Path(f'outputs/base-{N}-{d}-{closed}.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
