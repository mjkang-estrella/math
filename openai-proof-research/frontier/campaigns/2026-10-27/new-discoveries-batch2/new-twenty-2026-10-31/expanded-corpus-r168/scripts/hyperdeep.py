import pathlib,json,random,functools,time,math
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(168);start=time.monotonic();out=[]
def count(es,n):
 @functools.lru_cache(None)
 def f(edges):
  if not edges:return 1
  if edges[0]==0:return 0
  universe=0
  for e in edges:universe|=e
  v=max((1<<i for i in range(n) if universe>>i&1),key=lambda b:sum(bool(e&b) for e in edges))
  a=tuple(e for e in edges if not e&v);b=tuple(sorted(set(e&~v for e in edges)))
  ua=ub=0
  for e in a:ua|=e
  for e in b:ub|=e
  return (f(a)<<(universe.bit_count()-1-ua.bit_count()))+(f(b)<<(universe.bit_count()-1-ub.bit_count()))
 u=0
 for e in es:u|=e
 return f(tuple(sorted(es)))<<(n-u.bit_count())
for r,n in [(3,9),(3,12),(3,15),(3,18),(4,12),(4,16),(4,20),(6,12),(6,18),(6,24)]:
 for d in (2,3,4,6):
  best=None;total=0;maxratio=0
  for trial in range(80):
   es=[]
   for j in range(d):
    for retry in range(100):
     vs=list(range(n));rng.shuffle(vs);new=[sum(1<<v for v in vs[k:k+r]) for k in range(0,n,r)]
     if not set(es)&set(new):es+=new;break
    else:break
   if len(es)!=n*d//r:continue
   # random degree-preserving endpoint switches destroy initial r-partite structure
   for _ in range(5*len(es)):
    i,j=rng.sample(range(len(es)),2);a,b=es[i],es[j];xs=[v for v in range(n) if a>>v&1 and not b>>v&1];ys=[v for v in range(n) if b>>v&1 and not a>>v&1]
    if not xs or not ys:continue
    x,y=rng.choice(xs),rng.choice(ys);aa=a^(1<<x)^(1<<y);bb=b^(1<<x)^(1<<y)
    if aa==bb or aa in es or bb in es:continue
    es[i],es[j]=aa,bb
   val=count(es,n);H=2**((r-1)*d)+(2**d-1)*(2**(r-1)-1)**d;total+=1
   ratio=val**(1/n)/H**(1/(r*d))
   if ratio>maxratio:maxratio=ratio;best={'edges':es,'independent_sets':val}
   if val**(r*d)>H**n:print('COUNTEREXAMPLE',r,n,d,best,flush=True);raise RuntimeError('witness')
   if time.monotonic()-start>105:break
  out.append({'r':r,'n':n,'d':d,'tested':total,'best_ratio_float':maxratio,'best':best,'all_comparisons_exact_integer':True})
  (D/'outputs/hyperdeep.json').write_text(json.dumps(out,indent=2));print(r,n,d,total,maxratio,flush=True)
  if time.monotonic()-start>105:raise SystemExit
