import sys,json,numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
from itertools import combinations
from pathlib import Path
N=int(sys.argv[1]);d=int(sys.argv[2]);edges=list(combinations(range(N),2));M=len(edges);n=N.bit_length()-1
A=lil_matrix((N*(n+1),M+N*n));rhs=np.zeros(N*(n+1));rhs[:N]=d
for j,(u,v) in enumerate(edges):
 A[u,j]=A[v,j]=1
 for bit in range(n):
  if v>>bit&1:A[N+u*n+bit,j]=1
  if u>>bit&1:A[N+v*n+bit,j]=1
for v in range(N):
 for bit in range(n):A[N+v*n+bit,M+v*n+bit]=-2
res=milp(np.zeros(M+N*n),integrality=np.ones(M+N*n),bounds=Bounds(np.zeros(M+N*n),np.r_[np.ones(M),np.full(N*n,d//2)]),constraints=LinearConstraint(A.tocsr(),rhs,rhs),options={'time_limit':20,'mip_rel_gap':0})
r={'N':N,'d':d,'status':int(res.status),'message':res.message,'search':'all identity-labelled adjacency matrices; parity integer variables; connectedness checked after solving'}
if res.x is not None:
 E=[(u,v) for j,(u,v) in enumerate(edges) if res.x[j]>.5];neigh=[[v if u==x else u for u,v in E if x in (u,v)] for x in range(N)];reach={0}
 while True:
  rr=reach|{y for x in reach for y in neigh[x]}
  if rr==reach:break
  reach=rr
 from functools import reduce
 from operator import xor
 ok=all(len(a)==d and reduce(xor,a,0)==0 for a in neigh)
 r.update(edges=E,exact_open_xor_verified=ok,connected=len(reach)==N,closed_complement_degree=N-1-d)
Path(f'outputs/xor-{N}-{d}.json').write_text(json.dumps(r,indent=2)+'\n');print(r,flush=True)
