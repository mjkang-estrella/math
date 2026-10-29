"""Exact finite diagnostic. No all-n theorem is asserted."""
import itertools, collections, json, pathlib, resource, random
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(45,45))

def data(n):
 edges=list(itertools.combinations(range(n),2)); E=len(edges)
 def cross(e,f):
  a,b=e;c,d=f
  return a<c<b<d or c<a<d<b
 crosses=[sum(1<<j for j,f in enumerate(edges) if cross(e,f)) for e in edges]
 trees=[]
 for ix in itertools.combinations(range(E),n-1):
  mask=sum(1<<i for i in ix)
  if any(crosses[i]&mask for i in ix):continue
  p=list(range(n))
  def root(x):
   while p[x]!=x:x=p[x]
   return x
  for i in ix:
   a,b=map(root,edges[i])
   if a==b:break
   p[a]=b
  else:trees.append(mask)
 index={m:i for i,m in enumerate(trees)}; adj=[[] for _ in trees]
 for k,m in enumerate(trees):
  for i in range(E):
   if not m>>i&1:continue
   rem=m^(1<<i)
   for j in range(E):
    if m>>j&1 or crosses[j]&rem:continue
    z=index.get(rem|(1<<j))
    if z is not None:adj[k].append(z)
 return edges,trees,adj

def bfs(adj,trees,s,h=0):
 dist=[-1]*len(trees);dist[s]=0;q=collections.deque([s])
 while q:
  u=q.popleft()
  for v in adj[u]:
   if dist[v]<0 and trees[v]&h==h:dist[v]=dist[u]+1;q.append(v)
 return dist
out=[]
for n in range(3,9):
 edges,ts,adj=data(n)
 assert len(ts)=={3:3,4:12,5:55,6:273,7:1428,8:7752}[n]
 starts=list(range(len(ts))) if n<=7 else sorted(random.Random(3401).sample(range(len(ts)),24))
 tests=0;faces=0;maxratio=(0,None);maxdiam=0
 for s in starts:
  m=ts[s];d=bfs(adj,ts,s);assert min(d)>=0;maxdiam=max(maxdiam,max(d))
  h=m
  while h:
   dh=bfs(adj,ts,s,h);faces+=1
   for t in range(len(ts)):
    if m&ts[t]!=h:continue
    tests+=1
    assert d[t]==dh[t],('COUNTEREXAMPLE',n,s,t,h,d[t],dh[t])
   h=(h-1)&m
  for t in range(len(ts)):
   delta=(m^ts[t]).bit_count()//2
   if delta and d[t]/delta>maxratio[0]:maxratio=(d[t]/delta,{'source':[edges[i] for i in range(len(edges)) if m>>i&1], 'target':[edges[i] for i in range(len(edges)) if ts[t]>>i&1], 'distance':d[t], 'delta':delta})
 out.append(dict(n=n,trees=len(ts),directed_adjacencies=sum(map(len,adj)),sources=len(starts),source_indices=starts,nonempty_common_ordered_pairs=tests,face_bfs=faces,max_distance_from_checked_sources=maxdiam,max_ratio=maxratio))
 print(json.dumps(out[-1]),flush=True)
# Elementary source-admissible obstruction to ONE-FLIP edge-insertion normalization.
edges,ts,adj=data(6);e=(0,3);T={(0,1),(1,2),(1,3),(1,4),(1,5)}
m=sum(1<<edges.index(x) for x in T); assert m in ts
assert all(not(ts[j]>>edges.index(e)&1) for j in adj[ts.index(m)])
print('one-flip insertion obstruction PASS: e=(0,3), T=',sorted(T),flush=True)
pathlib.Path(__file__).with_name('check-results.json').write_text(json.dumps(out,indent=2)+'\n')
