import itertools,random,json,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));rng=random.Random(95004)
def copies(n,es,stars):
 adj=[set() for _ in range(n)]
 for a,b in es:adj[a].add(b);adj[b].add(a)
 def rec(i,used):
  if i==len(stars):return True
  d=stars[i]
  for c in range(n):
   if used>>c&1:continue
   nei=[v for v in adj[c] if not used>>v&1]
   for ls in itertools.combinations(nei,d):
    new=used|1<<c
    for v in ls:new|=1<<v
    if rec(i+1,new):return True
  return False
 return rec(0,0)
def arrows(n,es,A,B):
 m=len(es)
 # Include constant colorings; witness coloring is enough to reject a host.
 for mask in range(1<<m):
  red=[e for i,e in enumerate(es) if mask>>i&1];blue=[e for i,e in enumerate(es) if not mask>>i&1]
  if not copies(n,red,A) and not copies(n,blue,B):return False
 return True
for A,B,n in [([2,1],[2,1],6),([3,1],[2,1],7),([3,2],[2,1],8),([3,2],[3,1],8),([4,1],[2,1],8)]:
 predicted=sum(max(A[i]+B[k-i]-1 for i in range(len(A)) if 0<=k-i<len(B)) for k in range(len(A)+len(B)-1));m=predicted-1;pairs=list(itertools.combinations(range(n),2));tested=0;hits=[]
 hosts=itertools.combinations(pairs,m) if A==B==[2,1] else (rng.sample(pairs,m) for _ in range(1500))
 for es in hosts:
  tested+=1
  if arrows(n,list(es),A,B):hits.append(es);break
 print(json.dumps({'A':A,'B':B,'n':n,'host_edges':m,'conjectured_size':predicted,'hosts_tested':tested,'exhaustive_hosts':A==B==[2,1],'arrow_hits':hits}),flush=True)
