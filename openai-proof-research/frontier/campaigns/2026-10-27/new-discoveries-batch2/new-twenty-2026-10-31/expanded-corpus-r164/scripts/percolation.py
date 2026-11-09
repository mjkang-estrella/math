import pathlib,itertools,json,random,sys,time
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(164)
def plane(q):
 add=(lambda a,b:a^b) if q==4 else (lambda a,b:(a+b)%q)
 def mul(a,b):
  if q!=4:return a*b%q
  v=0
  while b:
   if b&1:v^=a
   b>>=1;a<<=1
   if a&4:a^=7
  return v
 def dot(a,b):
  x=0
  for u,v in zip(a,b):x=add(x,mul(u,v))
  return x
 P=[(1,a,b) for a in range(q) for b in range(q)]+[(0,1,a) for a in range(q)]+[(0,0,1)]
 L=[sum(1<<i for i,p in enumerate(P) if dot(l,p)==0) for l in P]
 assert len(set(L))==q*q+q+1 and all(l.bit_count()==q+1 for l in L)
 assert all((x&y).bit_count()==1 for x,y in itertools.combinations(L,2))
 return P,L
out=[]
for q in [4,5,7]:
 P,L=plane(q);N=len(P);full=(1<<N)-1
 for r in range(4,q+1):
  def step(a):
   b=a
   for l in L:
    if (a&l).bit_count()>=r:b|=l
   return b
  def closure(a):
   while 1:
    b=step(a)
    if b==a:return a
    a=b
  best=99;hist={};w=None
  for it in range(2000):
   # start full and remove greedily while preserving percolation
   a=full;order=list(range(N));rng.shuffle(order)
   for v in order:
    b=a&~(1<<v)
    if closure(b)==full:a=b
   t=0;b=a
   while b!=full:b=step(b);t+=1
   hist[t]=hist.get(t,0)+1;best=min(best,t)
   if t==2:
    assert all(closure(a&~(1<<v))!=full for v in range(N) if a>>v&1)
    w={'mask':a,'points':[P[v] for v in range(N) if a>>v&1],'round1':step(a),'deletion_closures':{str(v):closure(a&~(1<<v)) for v in range(N) if a>>v&1}};break
  rec={'q':q,'r':r,'trials':it+1,'time_histogram':hist,'witness':w,'plane_points':P,'lines':L};out.append(rec);(D/'outputs/percolation.json').write_text(json.dumps(out));print(q,r,it+1,hist,'found',bool(w),flush=True)
