import resource,random,functools,time,json
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
rng=random.Random(350596);start=time.monotonic();tested=0;nearest=None
for trial in range(200):
 n=rng.choice([12,14,16,18]); adj=[0]*n;cliques=[];omega=1
 for v in range(n):
  c=rng.choice(cliques) if cliques else []
  c=[u for u in c if rng.random()<.8];omega=max(omega,len(c)+1)
  for u in c:adj[v]|=1<<u;adj[u]|=1<<v
  cliques.append(c+[v])
 for k in [3,4,5,6]:
  def path(mask):
   def extend(v,seen,seq):
    if len(seq)==k:return seq
    a=adj[v]&mask&~seen
    while a:
     b=a&-a;a-=b;j=b.bit_length()-1;r=extend(j,seen|b,seq+[j])
     if r:return r
   a=mask
   while a:
    b=a&-a;a-=b;r=extend(b.bit_length()-1,b,[b.bit_length()-1])
    if r:return r
  @functools.lru_cache(None)
  def solve(mask):
   p=path(mask)
   if p is None:return 0
   return 1+min(solve(mask&~(1<<v)) for v in p)
  value=solve((1<<n)-1);den=omega+k-2;gap=(omega-1)*n-value*den;tested+=1
  if nearest is None or gap<nearest['gap']:nearest={'trial':trial,'n':n,'omega':omega,'k':k,'psi':value,'gap':gap,'adj':adj}
  if gap<0:print('COUNTEREXAMPLE',json.dumps(nearest),flush=True);raise SystemExit
 if trial%25==0:print(json.dumps({'trial':trial,'tested':tested,'nearest':nearest,'elapsed':time.monotonic()-start}),flush=True)
print(json.dumps({'tested':tested,'nearest':nearest,'elapsed':time.monotonic()-start,'conclusion':'No counterexample; bounded seeded sample only.'}),flush=True)
