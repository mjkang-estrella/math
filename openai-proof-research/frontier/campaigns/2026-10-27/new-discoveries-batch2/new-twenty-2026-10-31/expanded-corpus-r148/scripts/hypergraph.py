import random,itertools,json,pathlib,time,sys
L=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(int(sys.argv[1]));out=[]
for n,trials in [(9,80),(10,80),(11,80),(12,60)]:
 full=(1<<n)-1;cols=list(range(1<<(n-1))); allcols=(1<<len(cols))-1; kill={}
 for size in [3,5,7]:
  for vs in itertools.combinations(range(n),size):
   e=sum(1<<v for v in vs); b=0
   for i,c in enumerate(cols):
    if c&e in (0,e):b |=1<<i
   kill[e]=b
 best=(len(cols),[])
 for t in range(trials):
  edges=[]; alive=allcols
  for step in range(250):
   opts=[]
   for _ in range(160):
    size=rng.choice([3,5,5,5,7]);vs=rng.sample(range(n),size);e=sum(1<<v for v in vs)
    if any(e==f for f,h in edges):continue
    forced=0
    for f,h in edges:
     s=e&f
     if s and s&(s-1)==0 and not(s&h):forced|=s
    maxhead=(size-1)//2
    if forced.bit_count()>maxhead:continue
    need=maxhead-forced.bit_count();pool=[v for v in vs if not forced>>v&1];h=forced|sum(1<<v for v in rng.sample(pool,need))
    gain=(alive&kill[e]).bit_count()
    if gain:opts.append((gain,rng.random(),e,h))
   if not opts:break
   _,_,e,h=max(opts);edges.append((e,h));alive &=~kill[e]
   if not alive:break
  if alive.bit_count()<best[0]:best=(alive.bit_count(),edges);print(n,t,'best_remaining_colorings',best[0],flush=True)
  if not alive:break
 out.append({'n':n,'trials':trials,'best_remaining_colorings':best[0],'best_directed_edges':best[1]})
 (L/f'outputs/hypergraph-{sys.argv[1]}.json').write_text(json.dumps(out,indent=2))
