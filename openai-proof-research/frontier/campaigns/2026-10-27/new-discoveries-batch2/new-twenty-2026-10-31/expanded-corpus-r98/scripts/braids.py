import functools,itertools,random,json
from pathlib import Path
D=Path(__file__).resolve().parents[1]
@functools.lru_cache(None)
def words(p):
 if all(p[i]<p[i+1] for i in range(len(p)-1)):return [()]
 out=[]
 for i in range(len(p)-1):
  if p[i]>p[i+1]:
   q=list(p);q[i],q[i+1]=q[i+1],q[i];out.extend(w+(i,) for w in words(tuple(q)))
   if len(out)>150000:raise OverflowError
 return out
rng=random.Random(98353460);res=[]
for n in [4,5,6,9,10,12]:
 tests=[];skipped=0
 for trial in range(100):
  p=list(range(n))
  if n<7:rng.shuffle(p)
  else:
   for _ in range(12):
    i=rng.randrange(n-1);p[i],p[i+1]=p[i+1],p[i]
  try:ws=words(tuple(p))
  except OverflowError:skipped+=1;words.cache_clear();continue
  ix={w:i for i,w in enumerate(ws)};par=list(range(len(ws)))
  def root(i):
   while par[i]!=i:par[i]=par[par[i]];i=par[i]
   return i
  for w,i in ix.items():
   for j in range(len(w)-2):
    if w[j]==w[j+2] and abs(w[j]-w[j+1])==1:
     v=w[:j]+(w[j+1],w[j],w[j+1])+w[j+3:];a,b=root(i),root(ix[v]);par[a]=b
  b=len({root(i) for i in range(len(ws))});tests.append(dict(p=p,R=len(ws),B=b));assert 2*b>=len(ws),(p,len(ws),b)
  words.cache_clear()
 row=dict(n=n,tests=tests,skipped=skipped);res.append(row);print(n,'tested',len(tests),'skipped',skipped,'min ratio',min(x['B']/x['R'] for x in tests),flush=True)
(D/'outputs/braids.json').write_text(json.dumps(res,indent=2)+'\n')
