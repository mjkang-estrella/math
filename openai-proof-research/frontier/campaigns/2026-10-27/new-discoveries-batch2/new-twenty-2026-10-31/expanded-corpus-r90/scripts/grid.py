import numpy as np,json,sys
from scipy.optimize import linprog
from fractions import Fraction as F
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def bound(n):
 if n%2==0:return max(F(n*n-2*t*(t+1),1)/F(2*n-2*t-1,2) for t in range(n//2))
 return max([F(n*n+1-8*k*k,n-2*k) for k in range((n+1)//4+1) if n-2*k>0]+[F(n*n-1-8*(k*k+k),n-2*k-1) for k in range((n-1)//4+1) if n-2*k-1>0])
def run(n):
 orbits={}; ids=[]
 for i in range(n):
  row=[]
  for j in range(n):
   key=tuple(sorted((min(i,n-1-i),min(j,n-1-j))))
   if key not in orbits:orbits[key]=len(orbits)
   row.append(orbits[key])
  ids.append(row)
 m=len(orbits);count=np.bincount(np.array(ids).ravel(),minlength=m);A=[]
 def sep(x,sgn):
  dp={};paths={}
  for i in range(n):
   for jj in range(n):
    j=jj if sgn==1 else n-1-jj; prev=[(a,b) for a,b in [(i-1,j),(i,j-sgn)] if (a,b) in dp]
    q=max(prev,key=lambda q:dp[q]) if prev else None
    dp[i,j]=x[ids[i][j]]+(dp[q] if q else 0);paths[i,j]=(paths[q] if q else [])+[ids[i][j]]
  q=(n-1,n-1 if sgn==1 else 0)
  return dp[q],np.bincount(paths[q],minlength=m)
 x=np.ones(m)*2/(2*n-1)
 for it in range(2000):
  viol=False
  for s in [1,-1]:
   v,a=sep(x,s)
   if not A or v>2+1e-8:A.append(a);viol=True
  if not viol:break
  sol=linprog(-count,A_ub=np.array(A),b_ub=np.full(len(A),2.),bounds=(0,2),method='highs');assert sol.success,sol.message;x=sol.x
 else:raise RuntimeError('iteration cap')
 rat=[F(float(v)).limit_denominator(1000000) for v in x];mx=max(sep(rat,s)[0] for s in [1,-1]);val=sum(int(c)*v for c,v in zip(count,rat));b=bound(n)
 rec={'n':n,'iterations':it,'orbit_count':m,'constraints':len(A),'objective':str(val),'conjectured_bound':str(b),'max_path_weight':str(mx),'exceeds_bound_exactly':val>b and mx<=2,'weights':[str(v) for v in rat],'orbit_index':ids}
 (D/f'outputs/grid-{n}.json').write_text(json.dumps(rec,indent=2)+'\n');print(n,it,str(val),str(b),str(mx),rec['exceeds_bound_exactly'],flush=True)
for n in map(int,sys.argv[1:]):run(n)
