from pathlib import Path
from functools import lru_cache
import json,sys,time
L=Path(__file__).resolve().parents[1]
@lru_cache(None)
def parts(n,m=None):
 if n==0:return ((),)
 if m is None:m=n
 return tuple((k,)+r for k in range(1,min(n,m)+1) for r in parts(n-k,k))
@lru_cache(None)
def hooks(lam,k):
 t=len(lam);b=[lam[i]+t-i-1 for i in range(t)];s=set(b);out=[]
 for x in b:
  y=x-k
  if y<0 or y in s:continue
  c=sorted((s-{x})|{y},reverse=True);nu=tuple(z-t+i+1 for i,z in enumerate(c));nu=tuple(z for z in nu if z)
  out.append((nu,(-1)**sum(y<z<x for z in b)))
 return tuple(out)
@lru_cache(None)
def chi(lam,rho):
 if not rho:return int(not lam)
 return sum(s*chi(nu,rho[1:]) for nu,s in hooks(lam,rho[0]))
for n in range(int(sys.argv[1]),int(sys.argv[2])+1):
 st=time.time();ps=sorted(parts(n));even=[p for p in ps if (n-len(p))%2==0];lowest=None;bad=[]
 for lam in ps:
  total=0
  for mu in even:
   total+=chi(lam,mu)
   if total<0:bad.append([lam,mu,total]);break
  if bad:break
 print(json.dumps({'n':n,'partitions':len(ps),'prefixes':len(even),'bad':bad,'seconds':time.time()-st,'cache':str(chi.cache_info())}),flush=True)
 chi.cache_clear();hooks.cache_clear()
 if bad:break
