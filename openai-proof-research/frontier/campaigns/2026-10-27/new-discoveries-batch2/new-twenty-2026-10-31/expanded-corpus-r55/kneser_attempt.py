import os,resource,itertools,math,json,time
os.environ.update(OMP_NUM_THREADS='2',OPENBLAS_NUM_THREADS='2',MKL_NUM_THREADS='2');os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
start=time.monotonic()
def solve(n,k,m):
 sets=[sum(1<<x for x in t) for t in itertools.combinations(range(n),k)];N=len(sets);D=math.comb(n-k,k) if n>=2*k else 0
 # variables selected sets and max degree; selected i => selected neighbours <= z
 a=np.zeros((N+1,N+1));a[0,:N]=1
 for i,x in enumerate(sets):
  a[i+1,:N]=[int(x&y==0) for y in sets];a[i+1,i]=D;a[i+1,-1]=-1
 lo=np.full(N+1,-np.inf);hi=np.full(N+1,D,dtype=float);lo[0]=hi[0]=m
 res=milp(np.r_[np.zeros(N),1],integrality=np.ones(N+1),bounds=Bounds(np.zeros(N+1),np.r_[np.ones(N),D]),constraints=LinearConstraint(a,lo,hi),options={'time_limit':2,'mip_rel_gap':0})
 return {'n':n,'k':k,'m':m,'status':res.message,'degree':None if res.x is None else round(res.x[-1]),'lower_bound':getattr(res,'mip_dual_bound',None),'family':None if res.x is None else [list(i for i in range(n) if x>>i&1) for j,x in enumerate(sets) if res.x[j]>.5]}
for n,k in [(6,2),(7,2),(8,2),(8,3),(9,3),(10,3)]:
 for m in range(math.ceil(math.comb(n,k)/2),math.comb(n-1,k)+1):
  if time.monotonic()-start>95:print('budget stop',flush=True);raise SystemExit
  t=next(t for t in range(k,n+1) if math.comb(t,k)>=m)
  a=solve(t,k,m);b=solve(n,k,m);print(json.dumps({'compressed':a,'ambient':b,'diagnostic_only':True}),flush=True)
  if b['degree'] is not None and a['lower_bound'] is not None and b['degree']<a['lower_bound']-.1:print('POTENTIAL COUNTEREXAMPLE',flush=True);raise SystemExit
