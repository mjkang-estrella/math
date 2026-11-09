import pathlib,json,math,itertools,functools,time
D=pathlib.Path(__file__).resolve().parents[1];start=time.monotonic()
@functools.lru_cache(None)
def factor(n):
 o=[];p=2
 while p*p<=n:
  e=0
  while n%p==0:n//=p;e+=1
  if e:o.append((p,e))
  p+=1 if p==2 else 2
 if n>1:o.append((n,1))
 return tuple(o)
def divisors(n):
 out=[1]
 for p,e in factor(n):out=[a*p**k for a in out for k in range(e+1)]
 return out
@functools.lru_cache(None)
def inv(m):
 if m==1:return (2,) # omit self-loop
 if m%2:return ()
 primes=sorted(d+1 for d in divisors(m) if len(factor(d+1))==1 and factor(d+1)[0][1]==1)
 def go(j,rem):
  if j==len(primes):return [1] if rem==1 else []
  p=primes[j];out=go(j+1,rem)
  a=p-1;v=p
  while rem%a==0:
   out.extend(v*x for x in go(j+1,rem//a))
   a*=p;v*=p
  return out
 return tuple(sorted(x for x in go(0,m) if x>m))
trace={}
@functools.lru_cache(None)
def embed(m,shape):
 if not shape:return {str(m):[]}
 candidates=inv(m)
 if len(candidates)<len(shape):return None
 choices=[]
 for t in shape:
  choices.append([(x,embed(x,t)) for x in candidates if not t or x%2==0])
  choices[-1]=[(x,w) for x,w in choices[-1] if w is not None]
  if not choices[-1]:return None
 for combo in itertools.product(*choices):
  if len({x for x,w in combo})!=len(shape):continue
  o={str(m):[x for x,w in combo]}
  for x,w in combo:o.update(w)
  return o
 return None
def graph(k):
 adj=[[]]
 def add(v):
  w=len(adj);adj.append([v]);adj[v].append(w);return w
 def arm(v,depth):
  if depth==0:
   add(v);add(v);return
  for _ in range(2):
   w=v
   for z in range(3):w=add(w)
   arm(w,depth-1)
 for _ in range(3):
  w=0
  for z in range(3):w=add(w)
  arm(w,k-2)
 return adj
def shape(adj,v,parent=-1):
 return tuple(sorted(shape(adj,w,v) for w in adj[v] if w!=parent))
out=[]
# Source's D2 control then prospective higher-stage skeleton; no source-fidelity assertion for k>2.
for k in [2,3,4]:
 a=graph(k);leaf=next(v for v in range(len(a)) if len(a[v])==1)
 s=shape(a,leaf);w=embed(1,s)
 row={'stage':k,'order':len(a),'embedding':w,'inverse_cache':inv.cache_info()._asdict(),'embed_cache':embed.cache_info()._asdict(),'wall':time.monotonic()-start}
 out.append(row);print(json.dumps(row),flush=True)
 (D/'outputs/totient.json').write_text(json.dumps(out,indent=2))
