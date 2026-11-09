import numpy as np,pathlib,json
from scipy.optimize import differential_evolution
D=pathlib.Path(__file__).resolve().parents[1];rng=np.random.default_rng(97013);out=[];best=0;arg=None;tests=0
for n in [3,4,5,8,12,16]:
 for sample in range(500):
  A=np.eye(n)*.5;ii,jj=np.triu_indices(n,1);v=rng.beta(.3,.3,len(ii));A[ii,jj]=v;A[jj,ii]=1-v;p=rng.dirichlet(np.ones(n)*.3);B=2*A*p[None,:];f=[np.ones(n)]
  for k in range(1,65):f.append(B@f[-1])
  for k in [8,9,10,12,16,24,32,48,64]:
   for a in range(1,k):
    val=float(p@(f[a]*f[k-a]));tests+=1
    if val>best:best=val;arg=[n,sample,k,a]
    if val>1+1e-8:raise RuntimeError(('potential witness requires exactification',n,sample,k,a,val))
 out.append({'n':n,'samples':500,'max_ratio_so_far':best,'argmax':arg})
# nonlinear search in weighted 3-class kernels, all parameters in compact box.
opt=[]
for k,a in [(8,1),(8,4),(9,4),(12,6),(24,12),(32,1),(64,32)]:
 def obj(x):
  A=np.eye(3)*.5;A[0,1],A[0,2],A[1,2]=x[:3];A[1,0],A[2,0],A[2,1]=1-x[:3];p=np.array([x[3],(1-x[3])*x[4],(1-x[3])*(1-x[4])]);B=2*A*p[None,:];f=[np.ones(3)]
  for _ in range(k):f.append(B@f[-1])
  return -float(p@(f[a]*f[k-a]))
 r=differential_evolution(obj,[(0,1)]*5,seed=97013,maxiter=100,popsize=10,tol=1e-9,polish=True,workers=1)
 opt.append({'k':k,'split':a,'max_ratio':-r.fun,'x':r.x.tolist(),'evaluations':r.nfev})
 print(opt[-1],flush=True)
(D/'outputs/path-deep.json').write_text(json.dumps({'random':out,'tests':tests,'optimization':opt,'warning':'floating diagnostics, not universal TAS proof or exact counterexample'},indent=2)+'\n')
