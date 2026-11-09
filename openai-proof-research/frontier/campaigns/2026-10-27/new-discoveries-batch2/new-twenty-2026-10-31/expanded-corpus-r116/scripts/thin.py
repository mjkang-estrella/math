from itertools import product
from functools import lru_cache
import json,sys,time
from pathlib import Path
D=Path(__file__).resolve().parents[1];m=int(sys.argv[1]);p=int(sys.argv[2]);Lmin=int(sys.argv[3]);limit=int(sys.argv[4])
V=list(product(range(p),repeat=m));U=V[1:];allmask=(1<<len(U))-1
cols=[v for v in V[1:] if sum(v)<=m*p]; masks=[sum(1<<i for i,u in enumerate(U) if sum(a*b for a,b in zip(u,v))%p==0) for v in cols]
count=0;full=0;witness=[];nodes=0;t=time.monotonic()
def rank(C):
 a=[list(c) for c in C];k=0
 for j in range(m):
  z=next((i for i in range(k,len(a)) if a[i][j]%p),None)
  if z is None:continue
  a[k],a[z]=a[z],a[k];a[k]=[(x*pow(a[k][j],-1,p))%p for x in a[k]]
  for i in range(k+1,len(a)):
   f=a[i][j];a[i]=[(x-f*y)%p for x,y in zip(a[i],a[k])]
  k+=1
 return k
def rec(start,cap,C,cover):
 global count,full,nodes
 nodes+=1
 if nodes>limit:return
 if not any(cap):
  count+=1
  if len(C)>=Lmin and cover==allmask:
   full+=1
   if rank(C)==m:witness.append(C);print('WITNESS',C,flush=True)
  return
 if sum(cap)+len(C)<Lmin:return
 for j in range(start,len(cols)):
  v=cols[j]
  if all(x<=y for x,y in zip(v,cap)):rec(j,tuple(y-x for x,y in zip(v,cap)),C+[v],cover|masks[j])
rec(0,(p,)*m,[],0)
r={'p':p,'m':m,'min_length':Lmin,'nodes':nodes,'node_cap':limit,'complete':nodes<=limit,'height_one_column_multisets':count,'thin_before_full_rank':full,'witnesses':witness,'seconds':time.monotonic()-t};print(r,flush=True);(D/f'outputs/thin-{m}-{p}-{Lmin}.json').write_text(json.dumps(r,indent=2)+'\n')
