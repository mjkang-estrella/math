#!/usr/bin/env python3
"""Fixed-work exact diagnostics. No exhaustive tree or coloring enumeration."""
import os,resource
for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[key]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(45,45))
import random,json,time
from pathlib import Path
P=1000003
assert all(P%d for d in range(2,1001)) # exact primality: sqrt(P)<1001
rng=random.Random(319089)
def shape(n):
 if n==1:return None
 k=rng.randrange(1,n)
 return (shape(k),shape(n-k))
def bal(d):return None if d==0 else (bal(d-1),bal(d-1))
def comb(n,right):
 t=None
 for _ in range(n-1):t=(None,t) if right else (t,None)
 return t
def leaves(t):return 1 if t is None else leaves(t[0])+leaves(t[1])
def degree(t):return 1 if t is None else max(2*degree(t[0]),3*degree(t[1]))
def ev(t,x):
 if t is None:return x,[1]
 a,wa=ev(t[0],x);b,wb=ev(t[1],x)
 return (a*a+b*b*b)%P,[(2*a*w)%P for w in wa]+[(3*b*b*w)%P for w in wb]
def rank(a):
 a=[r[:] for r in a];nr=len(a);nc=len(a[0]);r=0
 for c in range(nc):
  j=next((i for i in range(r,nr) if a[i][c]),None)
  if j is None:continue
  a[r],a[j]=a[j],a[r];iv=pow(a[r][c],-1,P);a[r]=[(v*iv)%P for v in a[r]]
  for i in range(r+1,nr):
   z=a[i][c]
   if z:a[i]=[(u-z*v)%P for u,v in zip(a[i],a[r])]
  r+=1
  if r==nr:break
 return r
def encode(t):return 'x' if t is None else '('+encode(t[0])+','+encode(t[1])+')'
def main():
 start=time.monotonic();cases=[]
 ts=[bal(d) for d in range(1,7)]+[comb(n,r) for n in range(2,25) for r in [False,True]]+[shape(rng.randrange(4,33)) for _ in range(160)]
 for t in ts:
  n=leaves(t);a=[ev(t,x)[1] for x in range(1,2*n+6)]
  r=rank(a);cases.append(dict(shape=encode(t),leaves=n,degree=degree(t),rank=r))
 out=dict(status='diagnostic only; full rank proves Q-linear independence for each listed shape',prime=P,cases=len(cases),full_rank=sum(c['leaves']==c['rank'] for c in cases),deficient=[c for c in cases if c['leaves']!=c['rank']],max_leaves=max(c['leaves'] for c in cases),cpu_limit_seconds=45,address_space_bytes=512*1024**2,seconds=time.monotonic()-start,records=cases)
 Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k!='records'})
if __name__=='__main__':main()
