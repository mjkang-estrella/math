import math,json,time,functools,sys
from collections import Counter,deque
from pathlib import Path
START=time.monotonic(); deadline=START+float(sys.argv[2] if len(sys.argv)>2 else 75)
def phi(n):
 r=n; p=2
 while p*p<=n:
  if n%p==0:
   r-=r//p
   while n%p==0:n//=p
  p+=1
 if n>1:r-=r//n
 return r
def graph(A):
 V=set()
 for a in A:
  while a not in V:
   V.add(a); a=phi(a)
 g={a:set() for a in V}
 for a in V:
  b=phi(a); assert b in V
  if a!=b:g[a].add(b); g[b].add(a)
 return g
def canon(g,u,p=None):return '('+''.join(sorted(canon(g,v,u) for v in g[u] if v!=p))+')'
def model(k):
 g={0:set()}
 def node(p):
  v=len(g); g[v]={p};g[p].add(v);return v
 def arm(p,h):
  v=node(p)
  if h:
   w=node(v);x=node(w);arm(x,h-1);arm(x,h-1)
 for _ in range(3):arm(0,k-1)
 return g
def validate(A,k,center=None):
 g=graph(A); t=model(k)
 assert sum(map(len,g.values()))==2*(len(g)-1)
 centers=[u for u in g if canon(g,u)==canon(t,0)]
 assert centers and len(g)==len(t)
 c=centers[0];dist={c:0};q=deque([c])
 while q:
  u=q.popleft()
  for v in g[u]:
   if v not in dist:dist[v]=dist[u]+1;q.append(v)
 assert len(dist)==len(g)
 return {'k':k,'generators':A,'vertices':len(g),'edges':sum(map(len,g.values()))//2,'centers':centers,'layers':dict(sorted(Counter(dist.values()).items())),'parents':{str(u):phi(u) for u in sorted(g)},'canonical':canon(g,c)}
@functools.lru_cache(None)
def divisors(n):
 return sorted({v for d in range(1,math.isqrt(n)+1) if n%d==0 for v in (d,n//d)})
def prime(p):return p>=2 and all(p%d for d in range(2,math.isqrt(p)+1))
@functools.lru_cache(None)
def inv(m,lower=2):
 ans=[1] if m==1 else []
 for d in divisors(m):
  p=d+1
  if p<lower or not prime(p):continue
  rem=m//d;power=p
  while True:
   ans.extend(power*x for x in inv(rem,p+1))
   if rem%p:break
   rem//=p;power*=p
 return tuple(sorted(set(ans)))
def search(k):
 t=model(k);root=next(u for u in t if len(t[u])==1)
 def assign(u,parent,label,used):
  if time.monotonic()>deadline:raise TimeoutError
  if label in used:return
  used=used|{label};children=[v for v in t[u] if v!=parent]
  def siblings(i,chosen,acc):
   if i==len(children):yield acc;return
   v=children[i]
   for x in inv(label):
    if x<=label or x in chosen:continue
    for sub in assign(v,u,x,chosen):
     yield from siblings(i+1,chosen|set(sub.values()),acc|sub)
  yield from siblings(0,used,{u:label})
 try:
  labels=next(assign(root,None,1,set()))
  A=[labels[u] for u in t if len(t[u])==1 and labels[u]!=1]
  result=validate(A,k); result['seconds']=time.monotonic()-START
  return result
 except TimeoutError:return {'k':k,'status':'bounded search timeout; no nonexistence claim','seconds':time.monotonic()-START,'inv_cache':str(inv.cache_info())}
if sys.argv[1]=='check':
 A=[3,167,334,19577,31657,39154,63314,702085,983055,1048576,1123336,1975461,2370559,2633948,3352289,3561823,4182461,4741118,5019445,5866457,8031112,8364922,11732914]
 out=[validate([3,256,376,384,564],2),validate([63314,31657,39154,19577,21932,16449,16384,13107,334,167,3],3),validate(A,4)]
else:out=search(int(sys.argv[1]))
print(json.dumps(out,indent=2))
