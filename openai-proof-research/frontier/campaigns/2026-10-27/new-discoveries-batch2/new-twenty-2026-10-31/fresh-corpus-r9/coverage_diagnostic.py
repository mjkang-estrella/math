import numpy as np,json
from scipy.special import roots_legendre,roots_laguerre
from pathlib import Path
# t=A*u, angular theta=pi-s/v^2. Gauss Laguerre in s, u.
u,uw=roots_laguerre(96);s,sw=roots_laguerre(96)
def f(A,v,rho=0):
 ss=s[s<np.pi*v*v];w=sw[s<np.pi*v*v];th=np.pi-ss/v**2
 a=2*np.cos(th)*(np.pi-th)+np.sin(th)
 h=v/np.sqrt(np.pi)*a
 return A/(np.pi*v*v)*np.sum(w[:,None]*uw[None,:]*np.exp(-rho*A*u[None,:]-h[:,None]*np.sqrt(A*u)[None,:]))
out=[]
for v in [2,4,8,16,32]:
 for rho in [0,0.01,0.1]:
  mid=2*f(.5,v,rho); end=f(.25,v,rho)+f(.75,v,rho)
  out.append(dict(v=v,rho=rho,center=mid,endpoints=end,jensen_defect=mid-end))
p=Path(__file__).resolve().parent;(p/'coverage-diagnostic.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
