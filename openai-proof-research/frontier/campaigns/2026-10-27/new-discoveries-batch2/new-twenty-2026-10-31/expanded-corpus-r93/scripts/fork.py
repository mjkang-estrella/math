import itertools,random,json,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def check(nb):
 n=len(nb);full=(1<<n)-1
 for s in itertools.combinations(range(n),5):
  m=sum(1<<v for v in s);ds=sorted((nb[v]&m).bit_count() for v in s)
  if ds==[1,1,1,2,3]:
   # With this degree sequence a disconnected triangle+edge is impossible.
   return None
 clique=[0]*(1<<n);chrom=[0]*(1<<n);perfect=[True]*(1<<n)
 for s in range(1,1<<n):
  bit=s&-s;v=bit.bit_length()-1;rest=s^bit
  clique[s]=max(clique[rest],1+clique[rest&nb[v]])
  # exact chromatic via independent set removal, force least vertex into removed set
  best=n
  a=rest
  while True:
   sub=a|bit
   if all(not(nb[u]&sub) for u in range(n) if sub>>u&1):best=min(best,1+chrom[s^sub])
   if not a:break
   a=(a-1)&rest
  chrom[s]=best
  perfect[s]=chrom[s]==clique[s] and all(perfect[s^(1<<u)] for u in range(n) if s>>u&1)
  if not any(perfect[a] and clique[s^a]<clique[s] for a in range(s+1) if a&~s==0):return (s,clique[s],chrom[s])
 return True
rng=random.Random(930768);mode=sys.argv[1] if len(sys.argv)>1 else 'all';res=[]
for n in (range(1,7) if mode=='all' else range(7,11)):
 es=list(itertools.combinations(range(n),2));cnt=0;eligible=0
 gs=range(1<<len(es)) if mode=='all' else (rng.getrandbits(len(es)) for _ in range(3000))
 for g in gs:
  nb=[0]*n
  for j,(a,b) in enumerate(es):
   if g>>j&1:nb[a]|=1<<b;nb[b]|=1<<a
  ans=check(nb);cnt+=1
  if ans is not None:eligible+=1
  if ans not in [True,None]:print('WITNESS',n,g,ans,flush=True)
  if cnt%1000==0:print('progress',n,cnt,eligible,flush=True)
 print('COMPLETE',n,cnt,eligible,flush=True);res.append([n,cnt,eligible]);(D/f'outputs/fork-{mode}.json').write_text(json.dumps(res))
