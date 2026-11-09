import pathlib,itertools,random,collections,json,math,time
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(171375615);out=[]
for p,r in [(3,3),(7,2),(3,4)]:
 q=p*p;res=list(itertools.product(range(p),repeat=r));best=10**9;trace=[];proposals=0
 for restart in range(12):
  T=[tuple(x) if restart%3==0 else tuple(x[j]+p*rng.randrange(p) for j in range(r)) for x in res]
  sub=lambda a,b:tuple((a[i]-b[i])%q for i in range(r))
  counts=collections.Counter(sub(a,b) for a in T for b in T);cur=len(counts);rb=cur
  for iteration in range(1200):
   idx=rng.randrange(1,len(T));old=T[idx];new=list(old);j=rng.randrange(r);new[j]=(new[j]+p*rng.randrange(1,p))%q;new=tuple(new)
   changes=collections.Counter()
   for a,b in enumerate(T):
    if a==idx:continue
    changes[sub(old,b)]-=1;changes[sub(b,old)]-=1;changes[sub(new,b)]+=1;changes[sub(b,new)]+=1
   delta=sum((counts[d]+c>0)-(counts[d]>0) for d,c in changes.items());proposals+=1
   temp=max(.15,2.0*(1-iteration/1200))
   if delta<=0 or rng.random()<math.exp(-delta/temp):
    for d,c in changes.items():
     counts[d]+=c
     if not counts[d]:del counts[d]
    T[idx]=new;cur+=delta
   rb=min(rb,cur)
   if cur<best:best=cur;witness=list(T)
  trace.append(dict(restart=restart,minimum=rb,final=cur))
  result=dict(p=p,r=r,box=(2*p-1)**r,proposals=proposals,best=best,best_transversal=witness,restarts=trace)
  (D/f'outputs/transversal-local-{p}-{r}.json').write_text(json.dumps(result,indent=2)+'\n');print(p,r,restart,rb,best,flush=True)
