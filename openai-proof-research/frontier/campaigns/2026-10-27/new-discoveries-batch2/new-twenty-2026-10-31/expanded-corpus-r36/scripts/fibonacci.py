import itertools,json,resource,pathlib,time,collections
resource.setrlimit(resource.RLIMIT_AS,(1500*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(55,55))
L=pathlib.Path(__file__).resolve().parent.parent;out=[]
def valid(s,p,r,kind):
 if kind=='I':
  runs=[len(x) for x in s.split('0') if x]
  if runs and max(runs)>r:return False
  return all(len(x)>=p for x in s.strip('0').split('1') if x)
 pos=[i for i,c in enumerate(s) if c=='1'];chain=1
 for a,b in zip(pos,pos[1:]):
  if b-a<p:return False
  chain=chain+1 if b-a==p else 1
  if chain>r:return False
 return True
def connectivity(V,adj,delta):
 N=len(V)
 if N<2:return 0
 if delta==N-1:return delta
 def flow(u,v):
  cap=[{} for _ in range(2*N)]
  def edge(x,y,c):cap[x][y]=c;cap[y].setdefault(x,0)
  for x in range(N):
   edge(2*x,2*x+1,delta if x in (u,v) else 1)
   for y in adj[x]:edge(2*x+1,2*y,delta)
  ans=0;source=2*u+1;target=2*v
  while ans<delta:
   pred={source:None};q=collections.deque([source])
   while q and target not in pred:
    x=q.popleft()
    for y,c in cap[x].items():
     if c and y not in pred:pred[y]=x;q.append(y)
   if target not in pred:return ans
   y=target
   while y!=source:
    x=pred[y];cap[x][y]-=1;cap[y][x]+=1;y=x
   ans+=1
  return ans
 for u in range(N):
  for v in range(u):
   if v not in adj[u]:
    k=flow(u,v)
    if k<delta:return k
 return delta
for n in range(2,8):
 for p,r,kind in itertools.product(range(1,4),range(1,4),'IO'):
  V=[v for v in range(1<<n) if valid(format(v,f'0{n}b'),p,r,kind)];idx={v:i for i,v in enumerate(V)}
  adj=[{idx[v^(1<<i)] for i in range(n) if v^(1<<i) in idx} for v in V]
  delta=min(map(len,adj));k=connectivity(V,adj,delta)
  d=dict(n=n,p=p,r=r,kind=kind,vertices=len(V),delta=delta,kappa=k);out.append(d)
  if k<delta:print('WITNESS',d,flush=True)
 (L/'fibonacci-diagnostics.json').write_text(json.dumps(out,indent=2)+'\n');print('completed n',n,flush=True)
