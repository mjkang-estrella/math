import resource,itertools,functools,random,json,time
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
start=time.monotonic();rng=random.Random(350625)
for trial in range(120):
 n=4 if trial<64 else 5;q=4
 if trial<64:edges=[s for i,s in enumerate(itertools.combinations(range(n),2)) if trial>>i&1]
 else:edges=[s for k in [2,3] for s in itertools.combinations(range(n),k) if rng.random()<.35]
 if not edges:continue
 def make(restrict):
  @functools.lru_cache(None)
  def f(t,r,player):
   if all(sum(t[v] for v in e)>=q for e in edges):return 0
   if r==0:return f(t,q,1-player)
   options=[]
   for v in range(n):
    limit=min(r,max([q-sum(t[u] for u in e) for e in edges if v in e] or [0]))
    weights=[limit] if player and restrict else range(1,limit+1)
    for w in weights:
     if w<=0:continue
     a=list(t);a[v]+=w;options.append(w+f(tuple(a),r-w,player))
   return (max if player else min)(options)
  return f
 full=make(False);greedy=make(True)
 for t in itertools.product(range(q+1),repeat=n):
  a=full(t,q,1);b=greedy(t,q,1)
  if a>b:
   print(json.dumps({'trial':trial,'n':n,'q':q,'edges':edges,'t':t,'full_grid':a,'greedy_grid':b,'warning':'Grid diagnostic only, continuous Edge-hitter strategy may change values.'}),flush=True);raise SystemExit
 if trial%16==0:print('completed',trial,'elapsed',time.monotonic()-start,flush=True)
print('No gaps in bounded q4 grid test; not continuous game proof.',time.monotonic()-start)
