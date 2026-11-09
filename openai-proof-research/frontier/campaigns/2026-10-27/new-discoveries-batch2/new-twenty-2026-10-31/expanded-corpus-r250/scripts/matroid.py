import random,itertools,json,sys,time,functools
random.seed(250)
def rank(vs):
 piv={}
 for v in vs:
  while v:
   k=v.bit_length()-1
   if k in piv:v^=piv[k]
   else:piv[k]=v;break
 return len(piv)
start=time.monotonic()
for r,k,trials in [(2,2,300),(3,2,1500),(4,2,1500),(3,3,1000),(4,3,300),(5,2,500)]:
 n=r*k+1;eligible=0;pairs=0
 for trial in range(trials):
  cols=[random.randrange(1,1<<r) for _ in range(n)];bases={sum(1<<i for i in c) for c in itertools.combinations(range(n),r) if rank([cols[i] for i in c])==r}
  @functools.lru_cache(None)
  def part(mask):
   if not mask:return True
   v=mask&-mask
   return any(b&v and b&mask==b and part(mask^b) for b in bases)
  full=(1<<n)-1;good={}
  for x in range(n):
   m=full^(1<<x)
   if part(m):good[x]={b for b in bases if b&m==b and part(m^b)}
  if len(good)>1:eligible+=1
  for x,y in itertools.combinations(good,2):
   pairs+=1
   if not good[x]&good[y]:print(json.dumps(dict(counterexample=True,r=r,k=k,cols=cols,x=x,y=y)),flush=True);sys.exit()
 print(json.dumps(dict(rank=r,k=k,trials=trials,eligible=eligible,element_pairs=pairs,wall=time.monotonic()-start)),flush=True)
