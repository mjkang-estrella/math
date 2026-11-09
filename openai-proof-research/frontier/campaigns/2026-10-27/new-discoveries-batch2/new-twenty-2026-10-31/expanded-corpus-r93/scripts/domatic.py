import itertools,functools,json,sys,random
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def values(nb):
 n=len(nb);bound=min((b.bit_count()+2)//2 for b in nb);vals=[1,1]
 for k in range(2,bound+1):
  full=(1<<n)-1
  @functools.lru_cache(None)
  def w(ms,empty,turn):
   if any(not (b&(m|empty)) for b in nb for m in ms):return False
   if not empty:return True
   used=sum(bool(m) for m in ms)
   for v in range(n):
    if empty>>v&1:
     for c in range(min(k,used+1)):
      new=list(ms);new[c]|=1<<v;new=tuple(sorted(new,reverse=True))
      ans=w(new,empty^(1<<v),1-turn)
      if ans== (turn==0):return ans
   return bool(turn)
  for t in range(2):
   if w((0,)*k,full,t):vals[t]=k
 return vals
mode=sys.argv[1] if len(sys.argv)>1 else 'all'
res=[];rng=random.Random(930609)
for n in (range(1,7) if mode=='all' else range(7,11)):
 hist={};cnt=0;edges=list(itertools.combinations(range(n),2))
 gs=range(1<<len(edges)) if mode=='all' else (sum((rng.random()<.75)<<j for j in range(len(edges))) for _ in range(300))
 for g in gs:
  nb=[1<<i for i in range(n)]
  for j,(a,b) in enumerate(edges):
   if g>>j&1:nb[a]|=1<<b;nb[b]|=1<<a
  # A gap >=2 needs a value >=3. Source Proposition 2.1 excludes it otherwise.
  if min(b.bit_count() for b in nb)<4:cnt+=1;continue
  val=values(nb);key=str(val);hist[key]=hist.get(key,0)+1;cnt+=1
  if abs(val[0]-val[1])>1:print('WITNESS',n,g,val,flush=True);break
  if cnt%100==0:print('progress',n,cnt,hist,flush=True)
 print('COMPLETE',n,cnt,hist,flush=True);res.append([n,cnt,hist])
 (D/f'outputs/domatic-{mode}.json').write_text(json.dumps(res,indent=2))
