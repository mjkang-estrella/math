import itertools,json,random,time
from small_graphs import graphs,iota,iso,ind
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def product(a,b):
 n=len(a);m=len(b);out=[0]*(n*m)
 for u in range(n):
  for v in range(m):
   out[u*m+v]=sum(1<<(w*m+v) for w in range(n) if a[u]>>w&1)|sum(1<<(u*m+w) for w in range(m) if b[v]>>w&1)
 return out
def below(a,k):
 # Exact branch over a witness uncovered edge: every isolating set covers an endpoint.
 n=len(a);full=(1<<n)-1;closed=[a[v]|1<<v for v in range(n)]
 def rec(cov,left):
  rem=full^cov
  for u in range(n):
   if rem>>u&1 and (a[u]&rem):
    v=(a[u]&rem&-(a[u]&rem)).bit_length()-1;break
  else:return []
  if not left:return None
  opts=closed[u]|closed[v]
  for x in range(n):
   if opts>>x&1:
    ans=rec(cov|closed[x],left-1)
    if ans is not None:return [x]+ans
  return None
 return rec(0,k-1)
r=random.Random(891);pool=[]
for n in range(2,7):
 for mask,a in graphs(n):
  z=iota(a)
  if z>=2:pool.append((n,mask,a,z))
print('factor census',len(pool),flush=True)
# Disconnected factors included. All 5-vertex-or-smaller hard factors; seeded 6-vertex sample.
small=[p for p in pool if p[0]<=5];large=[p for p in pool if p[0]==6];r.shuffle(large);sel=small+large[:70]
count=0
for i,p in enumerate(sel):
 for q in sel[i:]:
  a=product(p[2],q[2]);s=below(a,p[3]*q[3]);count+=1
  if s is not None:
   print(json.dumps(dict(counterexample=True,p=p,q=q,witness=s)),flush=True);raise SystemExit
print(json.dumps(dict(counterexample=False,factors=len(sel),factor_small=len(small),factor_order6=70,pairs=count,seed=891)),flush=True)
