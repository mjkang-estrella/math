import sys
sys.path.insert(0,str(__import__('pathlib').Path(__file__).resolve().parents[2]/'fresh-corpus-r10/pydeps'))
import numpy as np,json,pathlib
from scipy.optimize import minimize
D=pathlib.Path(__file__).resolve().parents[1]; rng=np.random.default_rng(124);out=[]
alpha=np.sqrt(2)*np.pi/3;target=alpha*alpha-alpha
for dim in [4,8,16]:
 w=1/np.arange(1,dim+1,dtype=float)**2;pairs=[(i,j) for i in range(4) for j in range(i)]
 def cons(z):
  x=z[:-1].reshape(4,dim);return np.array([np.dot(w,(x[i]-x[j])**2)-z[-1] for i,j in pairs])
 def jac(z):
  x=z[:-1].reshape(4,dim);J=np.zeros((6,len(z)))
  for r,(i,j) in enumerate(pairs):J[r,i*dim:(i+1)*dim]=2*w*(x[i]-x[j]);J[r,j*dim:(j+1)*dim]=-2*w*(x[i]-x[j]);J[r,-1]=-1
  return J
 best=-1;bx=None
 for seed in range(30):
  z=np.r_[rng.integers(0,2,(4,dim)).ravel(),.5]
  r=minimize(lambda z:-z[-1],z,jac=lambda z:np.r_[np.zeros(len(z)-1),-1],bounds=[(0,1)]*(4*dim)+[(0,2)],constraints=[dict(type='ineq',fun=cons,jac=jac)],method='SLSQP',options={'maxiter':250,'ftol':1e-11})
  val=min(cons(r.x)+r.x[-1]);
  if val>best:best=val;bx=r.x[:-1].reshape(4,dim).tolist()
 o=dict(dim=dim,starts=30,best_squared_distance=best,conjectured_infinite_squared_distance=target,points_scaled=bx);out.append(o);print(o,flush=True)
(D/'outputs/hilbert.json').write_text(json.dumps(out,indent=2))
