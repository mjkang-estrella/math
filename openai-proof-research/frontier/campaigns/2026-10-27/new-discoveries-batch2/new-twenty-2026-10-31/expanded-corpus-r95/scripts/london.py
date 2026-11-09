import itertools,random,collections,json,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));rng=random.Random(95007)
def cross(a,b):return(a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def run(A):
 n=len(A);cs=[];topes=set()
 for i,j in itertools.combinations(range(n),2):
  v=cross(A[i],A[j]);sig=tuple((dot(v,a)>0)-(dot(v,a)<0) for a in A)
  assert sig.count(0)==2
  for sign in [1,-1]:
   s=tuple(sign*x for x in sig);cs.append(s)
   for x,y in itertools.product([1,-1],repeat=2):t=list(s);t[i]=x;t[j]=y;topes.add(tuple(t))
 adj=[[] for s in cs]
 for i,s in enumerate(cs):
  for j in range(i):
   t=cs[j]
   if sum(a==0 and b==0 for a,b in zip(s,t))==1 and not any(a*b<0 for a,b in zip(s,t)):adj[i].append(j);adj[j].append(i)
 def bfs(v,allowed):
  ds={v:0};q=collections.deque([v])
  while q:
   u=q.popleft()
   for w in adj[u]:
    if w in allowed and w not in ds:ds[w]=ds[u]+1;q.append(w)
  return ds
 full=[bfs(i,set(range(len(cs)))) for i in range(len(cs))];pairs=set();ok=set()
 for t in topes:
  vs={i for i,s in enumerate(cs) if all(a==0 or a==b for a,b in zip(s,t))}
  for i in vs:
   ds=bfs(i,vs)
   for j in vs:
    if j<i:
     pairs.add((j,i))
     if ds[j]==full[i][j]:ok.add((j,i))
 return {'cocircuits':len(cs),'topes':len(topes),'common_tope_pairs':len(pairs),'failures':sorted(pairs-ok)}
for n in [6,9,10,11,12,14,16,20]:
 for sample in range(5):
  A=[]
  for i in range(n):
   while True:
    a=(1,i,i*i) if sample==0 else tuple(rng.randrange(-50,51) for _ in range(3))
    if all(dot(cross(b,c),a)!=0 for b,c in itertools.combinations(A,2)) and a!=(0,0,0):break
   A.append(a)
  print(json.dumps({'n':n,'sample':sample,'normals':A,**run(A)}),flush=True)
