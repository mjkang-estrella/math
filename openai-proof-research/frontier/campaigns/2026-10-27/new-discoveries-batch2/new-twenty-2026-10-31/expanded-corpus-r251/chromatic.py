from pathlib import Path
from itertools import combinations
from functools import lru_cache
from math import comb
import random,json
L=Path(__file__).resolve().parent;r=random.Random(334732);rows=[]
def check(n,E):
 adj=[0]*n
 for a,b in E:adj[a]|=1<<b;adj[b]|=1<<a
 N=1<<n;ind=[False]*N;ind[0]=True
 for s in range(1,N):
  v=(s&-s).bit_length()-1;t=s&(s-1);ind[s]=ind[t] and not(adj[v]&t)
 @lru_cache(None)
 def part(s):
  if not s:return (1,)+(0,)*n
  v=s&-s;rest=s^v;t=rest;ans=[0]*(n+1)
  while True:
   if ind[t|v]:
    a=part(rest^t)
    for j in range(n):ans[j+1]+=a[j]
   if not t:break
   t=(t-1)&rest
  return tuple(ans)
 coeff=part(N-1);vals=[]
 for q in range(n+1):
  fall=1;z=coeff[0]
  for k in range(1,n+1):fall*=q-k+1;z+=coeff[k]*fall
  vals.append(z)
 h=[sum((-1)**j*comb(n+1,j)*vals[k-j] for j in range(k+1)) for k in range(n+1)]
 a=[sum(h[:i+1])-sum(h[n-i+1:]) for i in range(n+1)]
 b=[-sum(h[:i+1])+sum(h[n-i:]) for i in range(n)]
 return h,a,b
bad=[];count=0
for n in range(1,11):
 es=list(combinations(range(n),2));masks=range(1<<len(es)) if n<=5 else [r.getrandbits(len(es)) for _ in range(30)]
 for mask in masks:
  E=[e for j,e in enumerate(es) if mask>>j&1];h,a,b=check(n,E);count+=1
  if max(a)>0 or min(b)<0:bad.append({'n':n,'edges':E,'h':h,'a':a,'b':b})
 print('n',n,'complete',flush=True)
(L/'chromatic-results.json').write_text(json.dumps({'cases':count,'all_labelled_graphs_orders_1_to_5':1099,'sampled_graphs_per_order_6_to_10':30,'failures':bad},indent=2));print('cases',count,'failures',len(bad))
