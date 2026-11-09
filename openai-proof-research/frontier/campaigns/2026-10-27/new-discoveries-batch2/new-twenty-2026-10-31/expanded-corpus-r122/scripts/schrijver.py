import itertools,collections,json,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1]
def graph(n,k):
 V=[sum(1<<i for i in c) for c in itertools.combinations(range(n-k+1),k) for c in [tuple(x+j for j,x in enumerate(c))] if c[-1]-c[0]!=n-1]
 adj=[[] for _ in V]
 for i,x in enumerate(V):
  for j in range(i):
   if not x&V[j]:adj[i].append(j);adj[j].append(i)
 return V,adj
def diam(n,k):
 V,adj=graph(n,k);idx={v:i for i,v in enumerate(V)};seen=set();dia=0;witness=None;orbits=0
 for s,x in enumerate(V):
  if x in seen:continue
  orbits+=1
  for y in [x,sum(((x>>i)&1)<<(n-1-i) for i in range(n))]:
   for i in range(n):seen.add(((y<<i)|(y>>(n-i)))&((1<<n)-1))
  dist=[-1]*len(V);dist[s]=0;q=collections.deque([s])
  while q:
   u=q.popleft()
   for v in adj[u]:
    if dist[v]<0:dist[v]=dist[u]+1;q.append(v)
  assert min(dist)>=0
  m=max(dist)
  if m>dia:dia=m;witness=[V[s],V[dist.index(m)]]
 return {'n':n,'k':k,'vertices':len(V),'edges':sum(map(len,adj))//2,'dihedral_orbits':orbits,'diameter':dia,'diameter_pair':witness}
rows=[]
for k in range(int(sys.argv[1]),int(sys.argv[2])+1):
 for r in range(1,min(6,k-1)+1):
  n=2*k+r
  if n/(k+r)*__import__('math').comb(k+r,k)>6000:continue
  row=diam(n,k);rows.append(row);print(json.dumps(row),flush=True)
(D/('outputs/schrijver-'+sys.argv[1]+'.json')).write_text(json.dumps(rows,indent=2))
