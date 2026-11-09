import itertools,json,pathlib,random,time
L=pathlib.Path(__file__).resolve().parents[1]
def rank(xs):
 b={}
 for x in xs:
  while x:
   p=x.bit_length()
   if p in b:x^=b[p]
   else:b[p]=x;break
 return len(b)
r=4;N=1<<r;cnt=[0]*(1<<N)
for xs in itertools.combinations(range(1,N),r):
 if rank(xs)==r:cnt[sum(1<<x for x in xs)]=1
for bit in range(N):
 for s in range(1<<N):
  if s>>bit&1:cnt[s]+=cnt[s^(1<<bit)]
out=[]
for c in range(1,r):
 size=N-(1<<(r-c));target=((1<<N)-1)^((1<<(1<<(r-c)))-1);best=max(cnt[s] for s in range(1<<N) if s.bit_count()==size)
 out.append({'r':r,'c':c,'subsets':sum(1 for s in range(1<<N) if s.bit_count()==size),'proposed_bases':cnt[target],'maximum':best,'maximizers':sum(1 for s in range(1<<N) if s.bit_count()==size and cnt[s]==best)})
 print(out[-1],flush=True)
(L/'outputs/bases-data.json').write_text(json.dumps(out,indent=2))
