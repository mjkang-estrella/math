import json,time
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from math import factorial
from fractions import Fraction
def primes(n):
 return [p for p in range(2,n+1) if all(p%d for d in range(2,int(p**.5)+1))]
def val(n,p):
 c=0
 while n%p==0:c+=1;n//=p
 return c
for n in (40,60,80,100):
 ps=primes(n)
 A=np.array([[sum(val(k,p) for k in range(2,t+1))-t*val(t,p) for t in range(2,n+1)] for p in ps],dtype=float)
 # Split into two binary sets, disjoint by a per-column inequality.
 B=np.concatenate((A,-A),axis=1);l=np.zeros(2*(n-1));u=np.ones(2*(n-1))
 l[n-2]=u[n-2]=1;u[2*n-3]=0
 C=np.concatenate((np.eye(n-1),np.eye(n-1)),axis=1)
 start=time.monotonic()
 res=milp(np.ones(2*(n-1)),integrality=np.ones(2*(n-1)),bounds=Bounds(l,u),constraints=[LinearConstraint(B,0,0),LinearConstraint(C,0,1)],options={'time_limit':20,'mip_rel_gap':0.05,'threads':1})
 row={'n':n,'status':res.status,'message':res.message,'seconds':time.monotonic()-start}
 if res.x is not None:
  x=np.rint(res.x).astype(int);left=[t for t in range(2,n+1) if x[t-2]];right=[t for t in range(2,n+1) if x[n-1+t-2]]
  def prod(ts):
   r=Fraction(1)
   for t in ts:r*=Fraction(factorial(t),t**t)
   return r
  row.update(left=left,right=right,exact_equal=prod(left)==prod(right))
 print(json.dumps(row),flush=True)
 if row.get('exact_equal'):break
