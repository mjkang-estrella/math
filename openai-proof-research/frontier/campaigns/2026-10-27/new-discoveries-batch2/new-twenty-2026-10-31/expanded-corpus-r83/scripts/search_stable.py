from pathlib import Path
from math import comb
import time,json
D=Path(__file__).resolve().parents[1];start=time.monotonic();rows=[];nodes=0
# H-representation: nonnegative, total=2t, each cyclic r-window <=t.
def count(n,r,t):
 global nodes
 a=[];ans=0
 def rec(left):
  nonlocal ans
  global nodes
  nodes+=1
  if len(a)==n:
   if left==0 and all(sum(a[(i+j)%n] for j in range(r))<=t for i in range(n)):ans+=1
   return
  for v in range(min(t,left)+1):
   if len(a)>=r-1 and sum(a[len(a)-r+1:])+v>t:continue
   a.append(v);rec(left-v);a.pop()
 rec(2*t);return ans
for n in range(3,10):
 for r in range(1,(n-1)//2+1):
  if time.monotonic()-start>100:break
  E=[count(n,r,t) for t in range(n)]
  h=[sum((-1)**j*comb(n,j)*E[i-j] for j in range(i+1)) for i in range(n)]
  falling=False;ok=True
  for a,b in zip(h,h[1:]):
   if a>b:falling=True
   if falling and a<b:ok=False
  rows.append(dict(n=n,r=r,E=E,h=h,unimodal=ok));print(rows[-1],flush=True)
(D/'outputs/stable-search.json').write_text(json.dumps({'rows':rows,'nodes':nodes,'seconds':time.monotonic()-start,'scope':'all n=3..9, r=1..floor((n-1)/2) unless time cap; dimension n-1; even n=2r lower-dimensional endpoint excluded; no floating arithmetic'},indent=2))
