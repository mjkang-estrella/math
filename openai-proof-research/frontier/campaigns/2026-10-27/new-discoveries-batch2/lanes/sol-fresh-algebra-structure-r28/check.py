import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import resource,signal,json,itertools,random
from fractions import Fraction
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(50,50));signal.alarm(60)
rng=random.Random(20261029)
def reach(n,edges):
 r=[1<<i for i in range(n)]
 for i,j in edges:r[i]|=1<<j
 for k in range(n):
  for i in range(n):
   if r[i]>>k&1:r[i]|=r[k]
 return r
def connected(n,edges):return all(x==(1<<n)-1 for x in reach(n,edges+[(j,i) for i,j in edges]))
def acyclic(n,edges):
 indeg=[0]*n
 for i,j in edges:indeg[j]+=1
 todo=[i for i in range(n) if not indeg[i]];c=0
 while todo:
  i=todo.pop();c+=1
  for a,j in edges:
   if a==i:
    indeg[j]-=1
    if indeg[j]==0:todo.append(j)
 return c==n
def count(n,edges):
 # All nonzero-arrow supports, exact polynomial at q=0.
 ans=0
 for bits in range(1<<len(edges)):
  e=[v for k,v in enumerate(edges) if bits>>k&1]
  if len(e)>=n-1 and connected(n,e) and acyclic(n,e):ans+=(-1)**(len(e)-n+1)
 return ans
def lie(n,edges):
 # Squarefree PBW logarithm: clique polynomial of commuting generators.
 N=1<<n;den=[0]*N;den[0]=1
 for s in range(1,N):
  verts=[i for i in range(n) if s>>i&1];unseen=set(verts);comps=[]
  while unseen:
   start=min(unseen);comp={start};again=True
   while again:
    old=len(comp)
    for i,j in edges:
     if i in unseen and j in unseen and (i in comp or j in comp):comp|={i,j}
    again=len(comp)!=old
   unseen-=comp;comps.append(comp)
  valid=True
  for comp in comps:
   if len(comp)==1:continue
   e=[(i,j) for i,j in edges if i in comp and j in comp];r=reach(n,e)
   if any(not all(r[i]>>j&1 for j in comp) for i in comp):valid=False
  if valid:den[s]=(-1)**len(comps)
 # inverse then logarithm, using marked-coordinate derivative (no fractions).
 inv=[0]*N;inv[0]=1
 for s in range(1,N):
  t=s
  while t:
   inv[s]-=den[t]*inv[s^t];t=(t-1)&s
 full=N-1;mark=1;ans=0;t=full
 while t:
  if t&mark:ans-=den[t]*inv[full^t]
  t=(t-1)&full
 return ans
checked=0;bad=[]
for n in range(1,5):
 universe=[(i,j) for i in range(n) for j in range(n) if i!=j]
 for bits in range(1<<len(universe)):
  e=[v for k,v in enumerate(universe) if bits>>k&1]
  a=count(n,e);l=lie(n,e);checked+=1
  if a!=l:bad.append(dict(n=n,edges=e,count=a,lie=l))
# Reproducible five-vertex sparse sample.
for _ in range(80):
 n=5;u=[(i,j) for i in range(n) for j in range(n) if i!=j];e=rng.sample(u,rng.randrange(4,10))
 a=count(n,e);l=lie(n,e);checked+=1
 if a!=l:bad.append(dict(n=n,edges=e,count=a,lie=l))
cyclic=[(0,1),(1,2),(2,0)];transitive=[(0,1),(1,2),(0,2)]
result=dict(status='PASS' if not bad else 'MISMATCH',seed=20261029,checked=checked,bad=bad,orientation_falsifier=dict(cyclic=count(3,cyclic),acyclic=count(3,transitive)),limits=dict(address_space_MiB=512,cpu_seconds=50,wall_seconds=60,BLAS_threads=1),scope='loopless simple directed quivers; squarefree all-one dimension only; NOT full conjecture')
print(json.dumps(result,indent=2));(Path(__file__).parent/'checks.json').write_text(json.dumps(result,indent=2))
