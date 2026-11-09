"""Exact finite coefficient scan of BBK Conj 5.2; no infinite claim."""
import json,time
from pathlib import Path

def coeffs(num,den,M):
 a=[0]*(M+1); a[0]=1
 for d in den:
  for j in range(d,M+1): a[j]+=a[j-d]
 for d in num:
  for j in range(M,d-1,-1): a[j]-=a[j-d]
 return a

def scan():
 t=time.time(); cases=0
 for n in range(1,31):
  for k in range(n+2,2*n+42):
   # q^(2n+1) times series below is the exact difference.
   N=[2*(k-n-1)]+list(range(2*k+1,2*k+2*n-2,2))
   D=list(range(1,2*n+2,2)); M=4*n*(k+n)
   a=coeffs(N,D,M); cases+=1
   if min(a)<0:
    m=next(j for j,v in enumerate(a) if v<0)
    return dict(status='negative',k=k,n=n,degree=m+2*n+1,coefficient=a[m],cases=cases,seconds=time.time()-t)
  print('completed n',n,'cases',cases,flush=True)
 return dict(status='finite scan only; no negative',n_max=30,k_range='n+2 <= k <= 2n+41',max_degree_formula='2n+1+4n(k+n)',cases=cases,seconds=time.time()-t)
if __name__=='__main__':
 r=scan(); print(r); Path(__file__).with_suffix('.json').write_text(json.dumps(r,indent=2))
