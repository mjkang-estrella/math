from functools import lru_cache
from pathlib import Path
import json,sys
D=Path(__file__).resolve().parents[1]
def calc(lam,q):
 rank=sum(x>=i+1 for i,x in enumerate(lam));a=list(lam);lengths=[0]*lam[0]
 while a:
  lengths[lam[0]-a[0]]=a[0]+len(a)-1;a=[x-1 for x in a[1:]if x>1]
 lengths+= [0]*(lam[0]-len(lengths));h=lengths[0];k=lam[0]-1
 cells={(x,y)for y in range(h+1)for x in range(-(h+1-y),h+1-y)}
 for i in range(k+1):cells.remove((-h-1+2*i,0));cells.remove((-h+2*(i+lengths[i]),0))
 cells=sorted(cells,key=lambda c:(c[1],c[0]));index={c:i for i,c in enumerate(cells)};N=len(cells)
 @lru_cache(None)
 def f(mask):
  if not mask:return (1,)
  bit=mask&-mask;i=bit.bit_length()-1;x,y=cells[i];res=[]
  for c in [(x+1,y),(x,y+1)]:
   j=index.get(c)
   if j is None or not mask>>j&1:continue
   black=(x+y-h)%2==0;power=int(c[1]==y and black);wt=q**y if black else 1
   p=f(mask^bit^(1<<j))
   if len(res)<len(p)+power:res+=[0]*(len(p)+power-len(res))
   for z,v in enumerate(p):res[z+power]+=wt*v
  while res and not res[-1]:res.pop()
  return tuple(res)
 p=list(f((1<<N)-1));original=p[:];div=[]
 for i in range(rank):
  for j in range(rank-i):
   root=q**i
   quot=[0]*(len(p)-1)
   for z in range(len(p)-1,0,-1):quot[z-1]=p[z]-(root*quot[z]if z<len(quot)else 0)
   rem=p[0]-root*quot[0]if quot else p[0]
   div.append(rem);p=quot
 return dict(partition=lam,q=q,t=1,rank=rank,border_lengths=lengths,region_cells=N,polynomial_coefficients=original,remainders=div,quotient=p,quotient_nonnegative=all(x>=0 for x in p),memo_states=f.cache_info().currsize)
out=[]
for lam in [(2,2),(3,3,3),(4,3,3),(4,4,2),(5,3,2),(5,5),(4,4,3),(4,4,4),(5,4,3),(5,4,4),(5,5,3)]:
 for q in [1,2]:
  r=calc(lam,q);out.append(r);print(r,flush=True);(D/'outputs/domino.json').write_text(json.dumps(out,indent=2)+'\n')
