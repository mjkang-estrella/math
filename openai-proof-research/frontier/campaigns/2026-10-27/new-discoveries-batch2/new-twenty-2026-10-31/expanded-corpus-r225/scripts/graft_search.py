import random,pathlib,json,collections,math,time
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(310225)
def tree(n):
 code=[rng.randrange(n) for _ in range(n-2)];ds=[1]*n
 for x in code:ds[x]+=1
 es=[]
 for x in code:
  y=next(i for i,d in enumerate(ds) if d==1);es.append((x,y));ds[x]-=1;ds[y]-=1
 a,b=[i for i,d in enumerate(ds) if d==1];es.append((a,b));return es
# Gr_s is a rooted tree with root degree exactly c, so it splits into the c required pendant-root branches.
def graph(es,bs,c,s,t,k):
 edges=[(i,i+1) for i in range(s+t)];N=s+t+1
 for i in range(1,s+t):
  if i==s:continue
  for _ in range(c):edges.append((i,N));N+=1
 mp={0:s}
 for i in range(1,bs):mp[i]=N;N+=1
 edges += [(mp[u],mp[v]) for u,v in es]
 adj=[set() for _ in range(N+(k-2)*len(edges))]
 for j,(u,v) in enumerate(edges):
  ee=[u,v]+list(range(N+j*(k-2),N+(j+1)*(k-2)))
  for x in ee:
   for y in ee:
    if x!=y:adj[x].add(y)
 return adj
def rho(a):
 n=len(a);dist=[]
 for s in range(n):
  ds=[-1]*n;ds[s]=0;q=collections.deque([s])
  while q:
   u=q.popleft()
   for v in a[u]:
    if ds[v]<0:ds[v]=ds[u]+1;q.append(v)
  assert min(ds)>=0;dist.append(ds)
 x=[1.]*n
 for it in range(100):
  y=[sum(d*z for d,z in zip(row,x)) for row in dist];rat=[b/a for a,b in zip(x,y)];lo=min(rat);hi=max(rat)
  if hi-lo<1e-9:break
  scale=max(y);x=[v/scale for v in y]
 return (lo+hi)/2,hi-lo
minimum=(1e99,None);count=0
for n in range(4,15):
 bases=0
 for z in range(30):
  es=tree(n);c=sum(0 in e for e in es)
  if c<2 or c>4 or n-1<=c:continue
  bases+=1
  for s,t in [(2,2),(3,2),(3,3),(4,2),(4,3),(4,4)]:
   for k in (2,3):
    a,err=rho(graph(es,n,c,s,t,k));b,err2=rho(graph(es,n,c,s+1,t-1,k));gap=b-a;count+=1
    if gap<minimum[0]:minimum=(gap,{'base_n':n,'base_edges':es,'c':c,'s':s,'t':t,'k':k,'rho_before':a,'rho_after':b,'width_before':err,'width_after':err2})
    if gap<0:print('POTENTIAL',json.dumps(minimum),flush=True);raise SystemExit()
 print(json.dumps({'base_n':n,'accepted_bases':bases,'cumulative_comparisons':count,'minimum_gap':minimum}),flush=True)
