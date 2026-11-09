from pathlib import Path
import json,random,itertools,sys
from functools import lru_cache
D=Path(__file__).resolve().parents[1];rng=random.Random(218)
def mc(a):
 n=len(a);full=(1<<n)-1;good=[]
 for s in range(1,1<<n):
  if all(2*(a[v]&s).bit_count()>=a[v].bit_count() for v in range(n) if s>>v&1):good.append(s)
 byv=[[s for s in good if s>>v&1] for v in range(n)]
 @lru_cache(None)
 def f(s):
  if not s:return 0
  v=(s&-s).bit_length()-1
  return max([1+f(s^t) for t in byv[v] if t&s==t]+[-100])
 return f(full)
def connected(a):
 seen=1;old=0
 while old!=seen:
  old=seen
  for v in range(len(a)):
   if seen>>v&1:seen|=a[v]
 return seen==(1<<len(a))-1
rows=[]
for n,limit in ([(8,1000),(9,1000),(10,1000)] if sys.argv[1]=='majority' else [(8,3000),(10,3000),(12,3000),(16,1000)]):
 bad=[];critical=0;count=0;es=list(itertools.combinations(range(n),2))
 for it in range(limit):
  p=rng.choice([.15,.25,.4,.5,.65,.8]);a=[0]*n
  for u,v in es:
   if rng.random()<p:a[u]|=1<<v;a[v]|=1<<u
  count+=1
  if sys.argv[1]=='majority':
   c=mc(a);vals=[]
   for u,v in es:
    if a[u]>>v&1:
     b=a.copy();b[u]^=1<<v;b[v]^=1<<u;z=mc(b);vals.append(z)
     if z==c:break
   else:
    if vals:
     critical+=1
     if min(vals)<c<max(vals):bad.append({'adj':a,'mc':c,'deleted':vals})
  else:
   if not connected(a):continue
   def clique(s):
    if not s:return 0
    v=(s&-s).bit_length()-1;t=s^(1<<v)
    return max(clique(t),1+clique(t&a[v]))
   deg=[v.bit_count() for v in a];rhs=0
   for u,v in es:
    if a[u]>>v&1:
     c=2+clique(a[u]&a[v]);rhs+=2*(1-1/c)*(1/deg[u]+1/deg[v])
   x=[1.]*n
   for t in range(60):
    y=[deg[u]*x[u]+sum(x[v] for v in range(n) if a[u]>>v&1) for u in range(n)];q=sum(u*v for u,v in zip(x,y))/sum(u*u for u in x);mx=max(y);x=[v/mx for v in y]
   if q>rhs+1e-8:bad.append({'adj':a,'rayleigh':q,'rhs':rhs})
  if bad:break
 row={'mode':sys.argv[1],'n':n,'seed':218,'samples':count,'critical':critical,'violations':bad};rows.append(row);print(json.dumps(row),flush=True)
 (D/'logs'/('random-'+sys.argv[1]+'-results.json')).write_text(json.dumps(rows,indent=2))
 if bad:break
