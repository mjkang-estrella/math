import os
for v in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[v]='1'
import resource,time,itertools,json,pathlib,math
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,)*2);resource.setrlimit(resource.RLIMIT_CPU,(100,100))
import numpy as np
from scipy.optimize import minimize,milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
w=pathlib.Path(__file__).resolve().parent;start=time.monotonic();rng=np.random.default_rng(5101)
def matchings(v):
 if not v:yield [];return
 for j in range(1,len(v)):
  for m in matchings(v[1:j]+v[j+1:]):yield [(v[0],v[j])]+m
out=[]
# Exact enumeration of pairings; floating geometry and optimization remain diagnostics only.
for d,n in [(2,4),(2,6),(3,6),(3,8)]:
 best=None
 for t in range(35):
  x=rng.normal(size=(n,d));x[:,0]*=10**(t%5)
  ds=np.linalg.norm(x[:,None,:]-x[None,:,:],axis=2);r=min(ds[i,j] for i in range(n) for j in range(i));x=x/r;ds=ds/r
  m=max(matchings(list(range(n))),key=lambda m:sum(ds[i,j] for i,j in m))
  centers=np.array([(x[i]+x[j])/2 for i,j in m]);rad=np.array([ds[i,j]/2 for i,j in m])
  fun=lambda z:float(np.max(np.linalg.norm(z-centers,axis=1)-rad))
  sol=minimize(fun,centers.mean(axis=0),method='Nelder-Mead',options={'maxiter':1500,'xatol':1e-9,'fatol':1e-9})
  val=-sol.fun
  if best is None or val<best['inradius_upper_estimate']:best=dict(inradius_upper_estimate=val,points=x.tolist(),matching=m,solver_success=bool(sol.success),center=sol.x.tolist())
 out.append(dict(d=d,n=n,trials=35,best=best));print(json.dumps(out[-1]),flush=True)
# All integer grid triangles, exact max-norm integer distances. MILP is uncertified.
for a,b,L in [(1,2,5),(1,8,10),(2,7,10)]:
 pts=list(itertools.product(range(L),repeat=2));n=len(pts);dist=lambda p,q:max(abs(p[0]-q[0]),abs(p[1]-q[1]));edges=[]
 for i,j,k in itertools.combinations(range(n),3):
  if sorted([dist(pts[i],pts[j]),dist(pts[i],pts[k]),dist(pts[j],pts[k])])==[a,b,a+b]:edges.append((i,j,k))
 A=lil_matrix((n+3*len(edges)+1,3*n));lb=np.zeros(A.shape[0]);ub=np.ones(A.shape[0]);
 for i in range(n):A[i,3*i:3*i+3]=1;lb[i]=ub[i]=1
 for j,e in enumerate(edges):
  for c in range(3):
   row=n+3*j+c
   for i in e:A[row,3*i+c]=1
   ub[row]=2;lb[row]=-np.inf
 A[-1,0]=1;lb[-1]=ub[-1]=1
 sol=milp(np.zeros(3*n),integrality=np.ones(3*n),bounds=Bounds(0,1),constraints=LinearConstraint(A.tocsr(),lb,ub),options={'time_limit':6,'threads':1})
 rec=dict(a=a,b=b,grid=L,vertices=n,triangles=len(edges),status=int(sol.status),message=sol.message)
 if sol.x is not None:
  colors=np.argmax(sol.x.reshape(n,3),axis=1);rec['exact_validated_coloring']=all(len({int(colors[i]) for i in e})>1 for e in edges);rec['colors']=colors.tolist()
 out.append(rec);print(json.dumps(rec),flush=True)
(w/'diagnostics.json').write_text(json.dumps(dict(seed=5101,elapsed=time.monotonic()-start,results=out,proof_status='uncertified diagnostics, no Lean endpoint'),indent=2))
