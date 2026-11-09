import os,resource
resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
os.sched_setaffinity(0,{0,1})
import random,time,json,resource
from pathlib import Path
p=Path(__file__).resolve().parent;rng=random.Random(336130);t=time.monotonic();tried=eligible=0;by={}
def test(adj):
 global tried,eligible
 tried+=1;n=len(adj);full=(1<<n)-1;dist=[]
 for v in range(n):
  seen=1<<v;front=seen;ds=[99]*n;ds[v]=0
  for k in range(1,n):
   nxt=0
   for j in range(n):
    if front>>j&1:nxt|=adj[j]
   front=nxt&~seen;seen|=front
   for j in range(n):
    if front>>j&1:ds[j]=k
   if not front:break
  if max(ds)!=3:return
  dist.append(ds)
 eligible+=1;by[n]=by.get(n,0)+1
 far=[sum(1<<j for j in range(n) if dist[v][j]==3) for v in range(n)]
 # Shrinking cover members preserves A and B, so a valid cover can be made
 # disjoint. We search bipartitions, fixing vertex 0 in A by symmetry.
 for A in range(1,full,2):
  B=full^A
  if not any((B>>v&1) and not(adj[v]&A) for v in range(n)):continue
  if not any((A>>v&1) and not(adj[v]&B) for v in range(n)):continue
  if all((far[v]&(B if A>>v&1 else A)) or not(adj[v]&(B if A>>v&1 else A)) for v in range(n)):return A
 return False
found=None
# Include cycles and crown graphs, then seeded independent-edge samples.
for n in range(6,19):
 if n<=7:
  a=[(1<<((i+1)%n))|(1<<((i-1)%n)) for i in range(n)];test(a)
 for rep in range(3000):
  if time.monotonic()-t>85:break
  prob=rng.uniform(.12,.5);a=[0]*n
  for i in range(n):
   for j in range(i):
    if rng.random()<prob:a[i]|=1<<j;a[j]|=1<<i
  ans=test(a)
  if ans is False:found={'n':n,'adjacency_masks':a};break
 if found or time.monotonic()-t>85:break
out={'seed':336130,'tried':tried,'self_centered_diameter3':eligible,'by_n':by,'counterexample_to_cover_conditions':found,'elapsed':time.monotonic()-t,'maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'proof':False}
(p/'appendage-search.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
