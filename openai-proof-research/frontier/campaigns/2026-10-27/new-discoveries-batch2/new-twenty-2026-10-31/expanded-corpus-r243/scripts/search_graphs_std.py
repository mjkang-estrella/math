import random,json,time,itertools,sys
rng=random.Random(243);start=time.monotonic()
def blocks(adj,skip=None):
 n=len(adj);disc=[-1]*n;low=[0]*n;stack=[];out=[];clock=[0]
 def dfs(u,par):
  disc[u]=low[u]=clock[0];clock[0]+=1
  for v in adj[u]:
   if skip and {u,v}==set(skip):continue
   if disc[v]<0:
    stack.append((u,v));dfs(v,u);low[u]=min(low[u],low[v])
    if low[v]>=disc[u]:
     c=set()
     while True:
      x,y=stack.pop();c.update((x,y))
      if (x,y)==(u,v):break
     out.append(c)
   elif v!=par and disc[v]<disc[u]:stack.append((u,v));low[u]=min(low[u],disc[v])
 for u in range(n):
  if disc[u]<0:dfs(u,-1)
 return out
def chordless(a):
 return all(not any(u in c and v in c for c in blocks(a,(u,v))) for u in range(len(a)) for v in a[u] if u<v)
def check(a):
 n=len(a);vs=[v for v in range(n) if len(a[v])<=2];idx={v:i for i,v in enumerate(vs)};adj=[sum(1<<idx[w] for w in a[v] if w in idx) for v in vs];memo={0:0}
 def alpha(mask):
  if mask not in memo:
   i=(mask&-mask).bit_length()-1;memo[mask]=max(alpha(mask&~(1<<i)),1+alpha(mask&~((1<<i)|adj[i])))
  return memo[mask]
 v=alpha((1<<len(vs))-1)
 if 6*v<n:print(json.dumps({'counterexample':[sorted(s) for s in a],'alpha':v}),flush=True);sys.exit(2)
 return v
for n in range(1,7):
 pairs=list(itertools.combinations(range(n),2));cnt=0
 for z in range(1<<len(pairs)):
  a=[set() for _ in range(n)]
  for i,(u,v) in enumerate(pairs):
   if z>>i&1:a[u].add(v);a[v].add(u)
  seen={0}
  for _ in range(n):seen|=set().union(*(a[v] for v in seen))
  if len(seen)!=n or not chordless(a):continue
  check(a);cnt+=1
 print(json.dumps({'n':n,'labeled_connected_chordless':cnt,'all_labeled_graphs':1<<len(pairs),'counterexamples':0,'elapsed':time.monotonic()-start}),flush=True)
for n in [8,10,12,16,20,24,30]:
 best=1
 for rep in range(60):
  a=[set() for _ in range(n)]
  for v in range(1,n):u=rng.randrange(v);a[u].add(v);a[v].add(u)
  pairs=list(itertools.combinations(range(n),2));rng.shuffle(pairs)
  for u,v in pairs:
   if v in a[u]:continue
   a[u].add(v);a[v].add(u)
   if not chordless(a):a[u].remove(v);a[v].remove(u)
  best=min(best,check(a)/n)
 print(json.dumps({'n':n,'random_maximal_chordless':60,'best_ratio':best,'elapsed':time.monotonic()-start}),flush=True)
