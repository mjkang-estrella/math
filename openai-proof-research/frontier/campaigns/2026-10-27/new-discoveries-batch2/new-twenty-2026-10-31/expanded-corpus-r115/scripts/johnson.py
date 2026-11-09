import itertools,math,random,time,json
from pathlib import Path
D=Path(__file__).resolve().parents[1];rng=random.Random(115);rows=[]
def upper(n,k):
 def C(n,k):return math.comb(n,k) if n>=k>=0 else 0
 def f(t):return t*C(n-t,k-1)+t*sum(C((k-i)*t,k-i) for i in range(2,k+1))-sum(C((k-i-1)*t+1,k-i) for i in range(1,k))
 return max(f((n+1)//k),f((n+k-1)//k))-1
for n,k in [(6,3),(7,3),(8,3),(8,4),(9,3),(9,4),(10,3),(10,4)]:
 V=[sum(1<<i for i in s) for s in itertools.combinations(range(n),k)];N=len(V);adj=[sum(1<<j for j,w in enumerate(V) if (v^w).bit_count()==2) for v in V];best=N;bestorder=None;start=time.monotonic();trials=0
 while time.monotonic()-start<11:
  a=adj[:];rem=(1<<N)-1;order=[];width=0
  while rem:
   vv=[i for i in range(N) if rem>>i&1];deg={i:(a[i]&rem).bit_count() for i in vv};md=min(deg.values());cand=[i for i in vv if deg[i]<=md+(1 if trials%3==1 else 0)];v=rng.choice(cand);nb=a[v]&rem;width=max(width,nb.bit_count());order.append(v)
   if width>=best:break
   rem^=1<<v
   for u in vv:
    if nb>>u&1:a[u]|=nb&~(1<<u)
  trials+=1
  if len(order)==N and width<best:best=width;bestorder=order
 row=dict(n=n,k=k,vertices=N,source_bound=upper(n,k),heuristic_treewidth_upper_bound=best,trials=trials,elimination_order=bestorder);rows.append(row);print(json.dumps(row),flush=True);(D/'outputs/johnson.json').write_text(json.dumps(rows,indent=2)+'\n')
