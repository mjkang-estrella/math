# Exact labelled regular-complement enumeration; complement cliques = independent sets.
import pathlib,json,itertools,functools
D=pathlib.Path(__file__).resolve().parents[1]
def enum(n,r):
 adj=[0]*n;deg=[r]*n
 def go(v):
  if v==n:
   yield tuple(adj);return
  cand=[u for u in range(v+1,n) if deg[u]>0]
  if deg[v]<0 or deg[v]>len(cand):return
  for nb in itertools.combinations(cand,deg[v]):
   for u in nb:deg[u]-=1;adj[u]|=1<<v;adj[v]|=1<<u
   if all(0<=deg[u]<=n-v-2 for u in range(v+1,n)):yield from go(v+1)
   for u in nb:deg[u]+=1;adj[u]^=1<<v;adj[v]^=1<<u
 go0=go(0)
 yield from go0
def cliques(a):
 @functools.lru_cache(None)
 def c(s):
  if not s:return 1
  b=s&-s;j=b.bit_length()-1;t=s^b
  return c(t)+c(t&a[j])
 return c((1<<len(a))-1)
def structure(a,r):
 n=len(a);seen=0;z=0
 for j in range(n):
  if seen>>j&1:continue
  s=1<<j;old=0
  while s!=old:
   old=s
   for v in range(n):
    if s>>v&1:s|=a[v]
  seen|=s
  if s.bit_count()==r+1:z+=1
 return n-z*(r+1)<2*(r+1)
res=[]
for n in range(2,10):
 for r in range((n-2)//2+1):
  if n*r%2:continue
  total=0;mx=-1;sm=-1
  for a in enum(n,r):
   total+=1;c=cliques(a);mx=max(mx,c)
   if structure(a,r):sm=max(sm,c)
  o=dict(n=n,d=n-r-1,complement_degree=r,labelled_count=total,max_independent_sets=mx,max_structured=sm);res.append(o);print(o,flush=True)
  if mx>sm:raise RuntimeError('counterexample')
(D/'dense-coverage-corrected.json').write_text(json.dumps(res,indent=2)+'\n')
