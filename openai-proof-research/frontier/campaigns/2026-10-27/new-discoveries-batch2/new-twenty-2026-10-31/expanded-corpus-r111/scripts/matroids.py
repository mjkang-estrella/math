import pathlib,json,random,itertools
from functools import lru_cache
L=pathlib.Path(__file__).resolve().parents[1]
def add(a,b):return [ (a[i]if i<len(a)else 0)+(b[i]if i<len(b)else 0)for i in range(max(len(a),len(b)))]
def scale(a,c):return [c*x for x in a]
def mul(a,b):
 o=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):o[i+j]+=x*y
 return o
def test(vs):
 n=len(vs)
 @lru_cache(None)
 def span(s):
  if not s:return frozenset([0])
  i=(s&-s).bit_length()-1;ss=span(s^(1<<i));return ss|{x^vs[i]for x in ss}
 def rank(s):return len(span(s)).bit_length()-1
 flats=[]
 for s in range(1<<n):
  cl=sum(1<<i for i,v in enumerate(vs)if v in span(s))
  if cl==s:flats.append(s)
 full=(1<<n)-1
 @lru_cache(None)
 def interval(a,b):return tuple(f for f in flats if f&a==a and f&b==f)
 @lru_cache(None)
 def mob(a,b):return 1 if a==b else -sum(mob(a,f)for f in interval(a,b)if f!=b)
 @lru_cache(None)
 def char(a,b):
  r=rank(b)-rank(a);o=[0]*(r+1)
  for f in interval(a,b):o[r-rank(f)+rank(a)]+=mob(a,f)
  return o
 @lru_cache(None)
 def P(a,b):
  if a==b:return [1]
  r=rank(b)-rank(a);R=[0]
  for f in interval(a,b):
   if f!=a:R=add(R,mul(char(a,f),P(f,b)))
  return [R[r-j]if r-j<len(R)else 0 for j in range((r+1)//2)]
 @lru_cache(None)
 def Q(a,b):
  if a==b:return [1]
  R=[0]
  for f in interval(a,b):
   if f!=a:R=add(R,scale(mul(P(a,f),Q(f,b)),-(-1)**(rank(f)-rank(a))))
  while len(R)>1 and R[-1]==0:R.pop()
  assert len(R)<=(rank(b)-rank(a)+1)//2
  return R
 r=rank(full);Y=[0]*(r+1)
 for f in flats:
  q=scale(Q(0,f),(-1)**(r+rank(f))*mob(f,full));d=r-rank(f)
  for i,x in enumerate(q):Y[d+i]+=x
 assert Y==Y[::-1]
 return {'vectors':vs,'rank':r,'flats':len(flats),'Y':Y,'unimodal':all(Y[i]<=Y[i+1]for i in range(r//2))}
rng=random.Random(111);out=[]
for mask in range(1,128):out.append(test([i+1 for i in range(7)if mask>>i&1]))
for n in range(5,10):
 for _ in range(30):out.append(test(rng.sample(range(1,16),n)))
for n in range(5,9):
 for _ in range(10):out.append(test([rng.randrange(1,16)for i in range(n)]))
(L/'outputs/matroids.json').write_text(json.dumps(out,indent=2));print('CASES',len(out),'FAILURES',[x for x in out if not x['unimodal']])
