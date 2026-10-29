import os,resource,signal,itertools,collections,json,time,pathlib
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(40,40));signal.alarm(55)
start=time.monotonic()
def tree(path):return tuple(sorted(tuple(sorted(e)) for e in zip(path,path[1:])))
def adj(t,n):
 a=[[] for _ in range(n)]
 for u,v in t:a[u].append(v);a[v].append(u)
 return a
def slides(t,n):
 a=adj(t,n)
 for v in range(n):
  if len(a[v])!=1:continue
  w=a[v][0]
  for u in a[w]:
   if u!=v:yield tuple(sorted([e for e in t if e!=tuple(sorted((v,w)))]+[tuple(sorted((v,u)))]))
def splits(t,n):
 a=adj(t,n);full=(1<<n)-1;out=[]
 for u,v in t:
  seen={u};stack=[u]
  while stack:
   w=stack.pop()
   for x in a[w]:
    if {w,x}=={u,v} or x in seen:continue
    seen.add(x);stack.append(x)
  mask=sum(1<<x for x in seen);out.append(min(mask,mask^full))
 return sorted(out)
def transport(a,b,n):
 dp={0:0};full=(1<<n)-1
 for x in a:
  new={}
  for mask,c in dp.items():
   for j,y in enumerate(b):
    if mask>>j&1:continue
    z=(x^y).bit_count();v=c+min(z,n-z);m=mask|1<<j
    new[m]=min(v,new.get(m,10**9))
  dp=new
 return dp[(1<<len(a))-1]
for m in range(1,1001):
 assert 2*sum(min(2*k,m) for k in range(1,m))+m == (3*m*m)//2
 assert 2*sum(min(2*k,m) for k in range(1,m+1)) == (3*m*m)//2+m
for n in range(9,1001):
 m=n//2
 bound=(3*m*m)//2+(m if n%2 else 0)
 assert bound < n*n//2-n
results=[]
for n in [5,6,7]:
 src=tree(range(n));d={src:0};q=collections.deque([src]);edgechecks=0
 while q:
  t=q.popleft()
  for u in slides(t,n):
   if n<=6:
    a=splits(t,n);b=splits(u,n)
    # Verify exactly one cut token moves one label.
    aa=list(a);bb=list(b)
    for x in a:
     if x in bb: aa.remove(x);bb.remove(x)
    assert len(aa)==len(bb)==1
    assert min((aa[0]^bb[0]).bit_count(),n-(aa[0]^bb[0]).bit_count())==1
    edgechecks+=1
   if u not in d:d[u]=d[t]+1;q.append(u)
 assert len(d)==n**(n-2)
 far=max(d,key=d.get);srcs=splits(src,n)
 # All paths modulo reversal, n<=7 only. Exact assignment DP.
 mx=-1;witness=None;fartransport=transport(srcs,splits(far,n),n)
 for p in itertools.permutations(range(n)):
  if p[0]>p[-1]:continue
  u=tree(p);z=transport(srcs,splits(u,n),n)
  if z>mx:mx=z;witness=p
 results.append(dict(n=n,trees=len(d),path_eccentricity=max(d.values()),source=src,far=far,far_transport=fartransport,max_path_transport=mx,max_transport_path=witness,slide_split_checks=edgechecks))
print(json.dumps(dict(results=results,elapsed=time.monotonic()-start),indent=2))
