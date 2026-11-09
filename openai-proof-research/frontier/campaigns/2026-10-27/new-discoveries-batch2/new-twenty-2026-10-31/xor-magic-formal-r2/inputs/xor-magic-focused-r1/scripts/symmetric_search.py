import itertools,json
from pathlib import Path
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
N=32;d=6;n=5;E=list(itertools.combinations(range(N),2));unseen=set(E);orbits=[]
def T(u):return (u&~3)|[0,2,3,1][u&3]
while unseen:
 e=min(unseen);orb={e};f=tuple(sorted(map(T,e)))
 while f not in orb:orb.add(f);f=tuple(sorted(map(T,f)))
 orbits.append(sorted(orb));unseen-=orb
m=len(orbits);A=lil_matrix((N*(n+1),m+N*n));rhs=np.zeros(N*(n+1));rhs[:N]=d
for j,orb in enumerate(orbits):
 for u,v in orb:
  A[u,j]+=1;A[v,j]+=1
  for b in range(n):A[N+u*n+b,j]+=(v>>b)&1;A[N+v*n+b,j]+=(u>>b)&1
for u in range(N):
 for b in range(n):A[N+u*n+b,m+u*n+b]=-2;rhs[N+u*n+b]=-((u>>b)&1)
r=milp(np.zeros(m+N*n),integrality=np.ones(m+N*n),bounds=Bounds(np.zeros(m+N*n),np.r_[np.ones(m),np.full(N*n,3)]),constraints=LinearConstraint(A.tocsr(),rhs,rhs),options={'time_limit':60,'disp':True})
out=dict(N=N,d=d,closed=True,status=int(r.status),message=r.message,edge_orbits=m,symmetry='order 3 linear on low two bits')
if r.x is not None:out['edges']=sorted(e for j,orb in enumerate(orbits) if r.x[j]>.5 for e in orb)
Path('outputs/symmetric-32-6.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
