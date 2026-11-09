import os, pathlib, json, math
import numpy as np
from scipy.special import roots_jacobi, eval_jacobi
L=pathlib.Path(__file__).resolve().parent
rows=[]
for alpha,beta in [(1,-.5),(1.5,-.5),(2,-.5),(3,-.5),(5,-.5),(1,0),(2,0),(3,0),(5,0),(3,1),(5,1),(7,3)]:
 D=2*alpha+2
 for s in sorted(set([.02,.1,.25,.5,1,1.5,2,3, D-.5, max(.01,alpha-beta-1)])):
  if s>=D:continue
  vals=[]
  for N in [512,1024]:
   t,w=roots_jacobi(N,alpha-s/2,beta)
   theta=np.arccos(t)/2
   smooth=(theta/np.sqrt(1-t))**(-s)
   vals.append([float(np.dot(w,smooth*eval_jacobi(n,alpha,beta,t))/np.sum(w)/math.exp(math.lgamma(n+alpha+1)-math.lgamma(n+1)-math.lgamma(alpha+1))) for n in range(1,65)])
  rows.append({'alpha':alpha,'beta':beta,'D':D,'s':s,'integrals_1024':vals[1],'max_grid_disagreement':max(abs(a-b) for a,b in zip(*vals)),'negative_indices':[i+1 for i,x in enumerate(vals[1]) if x< -1e-9]})
(L/'jacobi-checks.json').write_text(json.dumps({'method':'Gauss-Jacobi weight alpha-s/2,beta; unnormalized coefficients; no interval certification','rows':rows},indent=2))
reversals=[]
for key in sorted(set((x['alpha'],x['beta']) for x in rows)):
 rr=sorted((x for x in rows if (x['alpha'],x['beta'])==key),key=lambda x:x['s'])
 reversals += [(key,a['s'],b['s']) for a,b in zip(rr,rr[1:]) if not a['negative_indices'] and b['negative_indices']]
print({'rows':len(rows),'tested_modes':64,'finite_test_reversals':reversals,'max_disagreement':max(x['max_grid_disagreement'] for x in rows)})
