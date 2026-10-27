#!/usr/bin/env python3
import numpy as np, math, json
from pathlib import Path
from scipy.optimize import differential_evolution

def conv(a,b):
 n=len(a);fa=np.poly(a);fb=np.poly(b);co=[]
 for k in range(n+1):
  co.append(sum(math.factorial(n-i)*math.factorial(n-k+i)/(math.factorial(n)*math.factorial(n-k))*fa[i]*fb[k-i] for i in range(k+1)))
 roots=np.roots(co)
 if max(abs(roots.imag))>1e-6:raise ArithmeticError((a,b,roots))
 return sorted(roots.real)

def score(a):
 a=np.asarray(a);d=a[:,None]-a[None,:];np.fill_diagonal(d,np.inf);return np.sum(1/d,axis=1)

def state(x,n):
 a=np.r_[0,np.cumsum(np.exp(x[:n-1]))];b=np.r_[0,np.cumsum(np.exp(x[n-1:]))]
 a-=a.mean();b-=b.mean();c=max(np.max(abs(a)),np.max(abs(b)))
 return a/c,b/c

def rho(x,n,p):
 a,b=state(x,n);c=conv(a,b)
 vals=[-math.log(sum(abs(score(r))**p))/(p-1) for r in [a,b,c]]
 return math.exp(vals[2]-np.logaddexp(vals[0],vals[1]))-1

out=[]
for n in [3,4,5]:
 for p in [1.2,1.5,1.8,1.95]:
  res=differential_evolution(lambda x:rho(x,n,p),[(-4,4)]*(2*n-2),maxiter=70,popsize=7,seed=2600+int(100*p)+n,polish=True,tol=1e-7)
  a,b=state(res.x,n);record={'n':n,'p':p,'rho':float(res.fun),'a':a.tolist(),'b':b.tolist()};out.append(record)
  print(json.dumps(record),flush=True)
  Path('pstam-screen.json').write_text(json.dumps(out,indent=2)+'\n')
