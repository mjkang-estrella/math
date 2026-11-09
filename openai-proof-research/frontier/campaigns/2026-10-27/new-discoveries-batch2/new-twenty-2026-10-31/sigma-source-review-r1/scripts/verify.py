import itertools,json,time,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
t0=time.monotonic()
def graphs(n):
 if n==1:yield [0];return
 for adj in graphs(n-1):
  for S in range(1<<(n-1)):
   if any((S>>i)&1 and adj[i]&S for i in range(n-1)):continue
   yield [adj[i]|(((S>>i)&1)<<(n-1)) for i in range(n-1)]+[S]
def connected(adj):
 seen=1
 while True:
  nxt=seen
  for i,a in enumerate(adj):
   if seen>>i&1:nxt|=a
  if nxt==seen:return seen==(1<<len(adj))-1
  seen=nxt
for n in range(1,9):
 total=con=non=0;maxs=-1;mingap=None
 B=max([a*(n-a)*(n-2*a)**2 for a in range(1,n)] or [0])
 for adj in graphs(n):
  total+=1
  if not connected(adj):continue
  con+=1;d=[a.bit_count() for a in adj];m=sum(d)//2;M=sum(x*x for x in d);D=n*m-M
  s=sum((d[i]-d[j])**2 for i in range(n) for j in range(i))
  assert s==n*M-4*m*m and s<=B
  # Construct actual complete-bipartite partition using neighbors of vertex 0.
  A=adj[0];U=(1<<n)-1
  cb=all(adj[i]==(U^A if A>>i&1 else A) for i in range(n))
  if n==1:cb=True
  if n<=7:
   triples=sum(((adj[i]>>j&1)+(adj[i]>>k&1)+(adj[j]>>k&1))==1 for i,j,k in itertools.combinations(range(n),3))
   assert triples==D
  if not cb:
   non+=1;mingap=D if mingap is None else min(mingap,D)
   assert D>=n-2 and s<B
  maxs=max(maxs,s)
 print(json.dumps(dict(n=n,total_triangle_free=total,connected=con,non_complete_bipartite=non,min_deficit_non_cb=mingap,max_sigma=maxs,complete_bipartite_max=B,elapsed=time.monotonic()-t0)),flush=True)
# Every possible triangle-free extension of a labeled P4.
path=[2,5,10,4];extensions=0
for S in range(16):
 if any(S>>i&1 and path[i]&S for i in range(4)):continue
 extensions+=1
 witnesses=[(i,j) for i,j in itertools.combinations(range(4),2) if ((path[i]>>j&1)+(S>>i&1)+(S>>j&1))==1]
 assert witnesses
 print('extension',S,'witnesses',witnesses)
# Binary search gives exact nearest bracketing pair; scaled integer inequality.
for n in range(7,100001):
 lo,hi=1,n//2
 while lo<hi:
  mid=(lo+hi)//2
  if 8*mid*(n-mid)>=n*n:hi=mid
  else:lo=mid+1
 candidates=[a for a in [lo-1,lo] if 1<=a<=n//2]
 assert any(16*a*(n-a)*(n-2*a)**2>=n**4-16*(n-3)**2 for a in candidates)
print('PASS bracketing 7..100000; all tests exact; elapsed',time.monotonic()-t0,'maxrss_KiB',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
