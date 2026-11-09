import itertools as it, random, time, json, sys, resource
import numpy as np
resource.setrlimit(resource.RLIMIT_CPU,(110,115)); resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
start=time.monotonic();rng=random.Random(1501)
def emit(**kw):print(json.dumps(kw),flush=True)
def ascount(w):
 s=set();n=len(w)
 for i in range(n):
  for h in range(1,(n-i)//2+1):
   if sorted(w[i:i+h])==sorted(w[i+h:i+2*h]):s.add(tuple(w[i:i+2*h]))
 return len(s)
if sys.argv[1]=='words':
 for n in range(1,10):
  checked=bad=0;best=0;first=None;overall=0
  def rec(w,mx):
   global checked,bad,best,first,overall
   if len(w)==n:
    checked+=1;v=ascount(w);overall=max(overall,v)
    if mx<=1:best=max(best,v)
    qb=max(ascount([0 if x==0 else (mask>>(x-1))&1 for x in w]) for mask in range(1<<mx))
    if qb<v:
     bad+=1
     if first is None:first=w
    return
   for c in range(mx+2):rec(w+[c],max(mx,c))
  rec([0],0);emit(n=n,canonical_words=checked,binary_max=best,all_alphabets_max=overall,quotient_failures=bad,first=first)
if sys.argv[1]=='fraction':
 for m,a,k,q in [(4,2,3,2),(5,2,3,2),(4,3,3,2),(4,2,3,3),(7,2,3,2),(5,2,4,2)]:
  colors=np.array([x for x in it.product(range(q+1),repeat=k) if sum(x)==q]);parts=np.array(list(it.combinations_with_replacement(range(len(colors)),a)));C=colors[parts];con=np.minimum(C[:,None,:,None,:],C[None,:,None,:,:]).sum(axis=(3,4));h=len(parts);best=100000;checked=0;itr=it.combinations_with_replacement(range(h),m)
  while True:
   batch=list(it.islice(itr,2000))
   if not batch:break
   P=np.array(batch);B=len(P);defect=np.zeros((B,m,a),int)
   for i in range(m):
    for j in range(m):
     if i!=j:defect[:,i,:]+=con[P[:,i],P[:,j],:]
   vals=defect.max(axis=(1,2)); j=int(vals.argmin())
   if int(vals[j])<best: best=int(vals[j]); witness=C[P[j]].tolist()
   checked+=B
  emit(m=m,a=a,k=k,denominator=q,part_types=h,configurations=checked,witness=witness,min_numerator=best,conjectured_numerator=((m+k-1)//k-1)*a*q)
if sys.argv[1]=='chip':
 for n in [11,13,15,17,21]:
  m=n//2;steps=sum(i*i for i in range(1,m+1));gene=[rng.getrandbits(32) for _ in range(steps)]
  def run(g):
   p={0:list(range(1,n+1))};t=0
   while True:
    active=sorted(x for x,v in p.items() if len(v)>1)
    if not active:break
    z=g[t];t+=1;x=active[z%len(active)];z//=len(active);v=p[x];a=z%len(v);z//=len(v);b=z%(len(v)-1);b+=b>=a;lo,hi=sorted((v[a],v[b]));a,b=sorted((a,b));v.pop(b);v.pop(a);p.setdefault(x-1,[]).append(lo);p.setdefault(x+1,[]).append(hi)
   w=[v[0] for x,v in sorted(p.items()) if v];assert len(w)==n and t==steps
   return sum(w[i]>w[j] for i in range(n) for j in range(i+1,n))
  score=run(gene);best=score;trials=0;local=time.monotonic()
  while time.monotonic()-local<13:
   g=gene.copy()
   for _ in range(1+rng.randrange(max(2,steps//10))):g[rng.randrange(steps)]=rng.getrandbits(32)
   v=run(g);trials+=1;best=max(best,v)
   if v>=score or rng.randrange(300)==0:gene,score=g,v
   if trials%1000==0:gene=[rng.getrandbits(32) for _ in range(steps)];score=run(gene)
   if v>m:emit(counterexample_n=n,inversions=v,gene=g);break
  emit(n=n,moves=steps,trials=trials,best_inversions=best,conjectured=m)
emit(seconds=time.monotonic()-start,ru_maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
