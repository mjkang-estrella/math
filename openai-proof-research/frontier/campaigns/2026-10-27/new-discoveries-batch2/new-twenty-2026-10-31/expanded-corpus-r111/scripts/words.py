from functools import lru_cache
from math import comb
import json,pathlib
L=pathlib.Path(__file__).resolve().parents[1]
def count(n,r,kind):
 @lru_cache(None)
 def f(c,seen,pairs):
  if not any(c):return 1
  total=0
  for z in range(n):
   if not c[z]:continue
   bad=False
   for a in range(n):
    for b in range(n):
     if pairs>>(a*n+b)&1 and ((kind==0 and a<b and (z==a or z>b)) or (kind==1 and ((a<b and a<z<b)or(a>b and z==a)))):bad=True;break
    if bad:break
   if bad:continue
   q=pairs
   for a in range(n):
    if seen>>a&1:q|=1<<(a*n+z)
   cc=list(c);cc[z]-=1;total+=f(tuple(cc),seen|1<<z,q)
  return total
 ans=f((r,)*n,0,0);return ans,f.cache_info().currsize
out=[]
for n,r in [(n,r) for n in range(1,7) for r in range(1,5) if n*r<=18]:
 form=sum(comb(n,i)* (comb(n+(r-1)*i-1,n-i) if n+(r-1)*i-1>=n-i else int(n-i==0))//(n-i+1) for i in []) if False else sum(__import__('fractions').Fraction(comb(n,i)*(comb(n+(r-1)*i-1,n-i) if n+(r-1)*i-1>=n-i else int(n-i==0)),n-i+1)for i in range(n+1))
 a,sa=count(n,r,0);b,sb=count(n,r,1);row={'n':n,'r':r,'123_121':a,'132_212':b,'formula':int(form),'states':[sa,sb]};out.append(row);print(row,flush=True)
 (L/'outputs/words.json').write_text(json.dumps(out,indent=2))
