import itertools,json,sys,time
# All simple cubic supergraphs of the directed Hamilton path 0,...,N-1.
# Additional degree: endpoints 2, internal 1. No added consecutive edge.
def threeconn(N,E):
 adj=[[] for _ in range(N)]
 for u,v in E:adj[u].append(v);adj[v].append(u)
 # Undirected unit-capacity local max flows from 0 to every other vertex.
 for t in range(1,N):
  c={(u,v):1 for u in range(N) for v in adj[u]}
  for _ in range(3):
   p={0:-1};Q=[0]
   for u in Q:
    for v in adj[u]:
     if c[u,v] and v not in p:p[v]=u;Q.append(v)
    if t in p:break
   if t not in p:return False
   v=t
   while v: u=p[v];c[u,v]-=1;c[v,u]+=1;v=u
 return True
for N in range(4,int(sys.argv[1])+1,2):
 d=[2]+[1]*(N-2)+[2];extra=[];cnt=over=qual=0;mx=0;found=[]
 f=[0,1,1]
 for _ in range(N):f.append(sum(f[-2:]))
 bound=f[N//2+2]+1
 def dfs():
  global cnt,over,qual,mx
  i=next((i for i in range(N) if d[i]),N)
  if i==N:
   cnt+=1;E=list(zip(range(N-1),range(1,N)))+extra
   p=[0]*N;p[0]=1
   for v in range(N):
    for a,b in E:
     if a==v:p[b]+=p[a]
   mx=max(mx,p[-1])
   if p[-1]>bound:
    over+=1
    if threeconn(N,E):qual+=1;found.append({'edges':E,'paths':p[-1]})
   return
  opts=[j for j in range(i+2,N) if d[j] and (i,j) not in extra]
  k=d[i]
  for J in itertools.combinations(opts,k):
   d[i]=0
   for j in J:d[j]-=1;extra.append((i,j))
   dfs()
   for j in reversed(J):d[j]+=1;extra.pop()
   d[i]=k
 dfs()
 print(json.dumps({'vertices':N,'Hamilton-supergraphs':cnt,'bound':bound,'unfiltered_max_paths':mx,'overbound':over,'three-edge-connected-overbound':qual,'witnesses':found[:3]}),flush=True)
