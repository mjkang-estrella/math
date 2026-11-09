from pathlib import Path
import numpy as np,json
from scipy.optimize import linear_sum_assignment
L=Path(__file__).parent;rng=np.random.default_rng(98231)
best=None;records=[]
N=100;u=(np.arange(N)+.5)/N
for trial in range(2400):
 knots=np.linspace(0,1,6)
 slopes=np.sort(rng.integers(1,31,size=(2,5)),axis=1)/10
 vals=np.column_stack([np.zeros(2),np.cumsum(slopes/5,axis=1)])
 q=np.array([np.interp(u,knots,v) for v in vals]);t=rng.choice([.5,.25,.1])
 r=np.array([t*q[0]+(1-t)*q[1],(1-t)*q[0]+t*q[1]])
 # 1-Lipschitz random polygonal payoff on sum support.
 hx=np.linspace(0,vals[:,-1].sum(),21);hy=np.r_[0,np.cumsum(rng.choice([-1,1],20)*np.diff(hx))]
 costs=[];perms=[]
 for x in [q,r]:
  c=np.interp(x[0,:,None]+x[1,None,:],hx,hy)
  i,j=linear_sum_assignment(c,maximize=True);costs.append(c[i,j].mean());perms.append(j)
 gap=costs[0]-costs[1]
 # Each pair's midpoint-quantile Wasserstein error <= max slopes sum/(2N).
 error=slopes[:,-1].sum()/N
 if best is None or gap>best['gap']:
  best=dict(trial=trial,N=N,slopes=slopes.tolist(),t=float(t),hx=hx.tolist(),hy=hy.tolist(),gap=float(gap),continuous_error_bound=float(error),old_permutation=perms[0].tolist())
 if gap>error+1e-8:break
(L/'diagnostic.json').write_text(json.dumps(best,indent=2));print(best)
