"""Exploratory finite necessary condition for BBK Conjecture 5.4, not a proof."""
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
import json
from pathlib import Path

def coeffs(k,n,M):
 a=[0]*(M+1);a[0]=1
 for d in range(1,2*n+2,2):
  for j in range(d,M+1):a[j]+=a[j-d]
 for d in range(2*k-1,2*k+2*n-2,2):
  for j in range(M,d-1,-1):a[j]-=a[j-d]
 return a

def run(k,n,M):
 rows=[];cols=[]
 for j,d in enumerate(range(1,2*n+2,2)):
  for t in range(M+1):
   for m in range(t,M+1,d):rows.append(m);cols.append(j*(M+1)+t)
 mat=coo_matrix((np.ones(len(rows)),(rows,cols)),shape=(M+1,(n+1)*(M+1))).tocsr()
 a=coeffs(k,n,M)
 # Farkas: A^T y >= 0, a.y < 0
 r=linprog(np.array(a,dtype=float),A_ub=-mat.T,b_ub=np.zeros(mat.shape[1]),bounds=[(-1,1)]*(M+1),method='highs')
 print(k,n,M,r.status,r.fun,flush=True)
 if r.success and r.fun < -1e-6:
  p=Path(__file__).with_name('partial_fraction_hit.json');p.write_text(json.dumps(dict(k=k,n=n,M=M,value=r.fun,y=r.x.tolist(),coeffs=a)));return True
 return False
if __name__=='__main__':
 for n in range(1,11):
  for k in range(n+2,n+15):
   if run(k,n,max(100,2*n*(k+n))):raise SystemExit
