import random,itertools,json,functools,sys
random.seed(144)
def parts(n,mn=2):
 if n==0:yield ();return
 for x in range(mn,n+1):
  for rest in parts(n-x,x):yield (x,)+rest
def cycle_masks(a):
 n=len(a);cs=[]
 for s in range(1,1<<n):
  if s.bit_count()<2:continue
  first=(s&-s).bit_length()-1
  states={(1<<first,first)}
  for _ in range(s.bit_count()-1):
   states={(t|1<<v,v) for t,u in states for v in range(n) if s>>v&1 and not t>>v&1 and a[u]>>v&1}
  if any(a[u]>>first&1 for t,u in states):cs.append(s)
 return cs
for n in (6,7,8):
 passed=0
 for it in range(200):
  # dense digraph, only retain ones satisfying the source total-degree hypothesis on W.
  a=[sum(1<<v for v in range(n) if v!=u and random.random()<.85) for u in range(n)]
  deg=[a[u].bit_count()+sum(a[v]>>u&1 for v in range(n)) for u in range(n)]
  cs=cycle_masks(a)
  for w in range(1,1<<n):
   if any(2*deg[u]<3*n-3 for u in range(n) if w>>u&1):continue
   for par in parts(w.bit_count()):
    @functools.lru_cache(None)
    def f(used,j):
     if j==len(par):return True
     return any(not s&used and (s&w).bit_count()==par[j] and f(used|s,j+1) for s in cs)
    assert f(0,0),(a,w,par)
    passed+=1
 print(json.dumps(dict(id=345351,n=n,draws=200,qualified_W_partition_cases=passed,bad=0)),flush=True)
# Hypergraph tight components (r-1 overlap), r=4.
for n in (4,5,6,7,8):
 es=list(itertools.combinations(range(n),4));masks=[sum(1<<x for x in e) for e in es]
 collist=itertools.product(range(4),repeat=len(es)) if n<=5 else ([random.randrange(4) for _ in es] for it in range(1000))
 count=0
 for colors in collist:
  seen=set();spans=False
  for i in range(len(es)):
   if i in seen:continue
   todo=[i];seen.add(i);union=0
   while todo:
    j=todo.pop();union|=masks[j]
    for k in range(len(es)):
     if k not in seen and colors[k]==colors[j] and (masks[k]&masks[j]).bit_count()==3:seen.add(k);todo.append(k)
   if union==(1<<n)-1:spans=True
  assert spans,(n,colors)
  count+=1
 print(json.dumps(dict(id=347962,r=4,n=n,colorings=count,exhaustive=n<=5,bad=0)),flush=True)
