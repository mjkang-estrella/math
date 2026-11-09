import sys,pathlib,json
sys.path.append('/home/mj-kang/.local/lib/python3.14/site-packages')
import numpy as np
from scipy.spatial import ConvexHull
D=pathlib.Path(__file__).resolve().parents[1];rng=np.random.default_rng(128)
def zp(v):
 x=np.zeros((1,3),dtype=np.int64)
 for w in v:x=np.concatenate((x-w,x+w))
 return x
for n in (3,4,5,6,7,8):
 best=0;pred=4*(1+n-1+(n-1)*(n-2)//2)-(n-2 if n%2==0 else 0)
 for trial in range(150):
  v=rng.integers(-20,21,(n,3));v=v*rng.integers(1,10,(n,1));z=zp(v);za=zp(v[:n//2]);zb=zp(v[n//2:]);q=np.concatenate((za,zb));
  # Reduce summands before Minkowski hull; these are actual factored zonoboxtopes (25).
  z=z[ConvexHull(z).vertices];q=q[ConvexHull(q).vertices]
  pts=(z[:,None,:]+q[None,:,:]).reshape(-1,3);count=len(ConvexHull(pts).vertices)
  if count>best:
   best=count;(D/f'outputs/maxout-n{n}-best.json').write_text(json.dumps(dict(n=n,trial=trial,generators=v.tolist(),vertices=count,predicted=pred))+'\n')
  if count>pred:print('POTENTIAL COUNTEREXAMPLE',n,trial,count,pred,flush=True);break
 print(dict(n=n,trials=trial+1,best=best,predicted=pred,qualification='integer construction, floating Qhull count only; no exact certificate'),flush=True)
