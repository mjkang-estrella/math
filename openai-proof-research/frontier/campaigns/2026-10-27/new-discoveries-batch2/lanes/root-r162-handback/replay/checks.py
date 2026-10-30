import itertools,random,json,sys
from functools import lru_cache
from pathlib import Path
L=Path(__file__).resolve().parent
def adj(n,edges):
 a=[0]*n
 for u,v in edges:a[u]|=1<<v;a[v]|=1<<u
 return a
def saturation(a):
 @lru_cache(20000)
 def f(mask):
  pair=None
  for u in range(len(a)):
   if mask>>u&1 and a[u]&mask:
    pair=(u,((a[u]&mask)&-(a[u]&mask)).bit_length()-1);break
  if pair is None:return 0
  opts=set()
  for u in pair:
   ns=a[u]&mask
   while ns:
    b=ns&-ns;ns-=b;opts.add((1<<u)|b)
  return 1+min(f(mask^p) for p in opts)
 result=f((1<<len(a))-1);f.cache_clear();return result
def indom(a):
 n=len(a);full=(1<<n)-1
 @lru_cache(None)
 def f(allowed,need):
  if not need:return 0
  v=(need&-need).bit_length()-1;opts=(a[v]|1<<v)&allowed
  best=n+1
  while opts:
   b=opts&-opts;opts-=b;u=b.bit_length()-1;closed=a[u]|b
   best=min(best,1+f(allowed&~closed,need&~closed))
  return best
 result=f(full,full);f.cache_clear();return result
def connected(a):
 seen=1
 while True:
  new=seen
  for u in range(len(a)):
   if seen>>u&1:new|=a[u]
  if new==seen:return seen==(1<<len(a))-1
  seen=new
def brute_s(a):
 n=len(a);best=n
 def rec(free,count,unmatched):
  nonlocal best
  if count>=best:return
  if not free:
   if all(not (a[u]&unmatched) for u in range(n) if unmatched>>u&1):best=count
   return
  b=free&-free;u=b.bit_length()-1
  rec(free^b,count,unmatched|b)
  ns=a[u]&free
  while ns:
   c=ns&-ns;ns-=c;rec(free^b^c,count+1,unmatched)
 rec((1<<n)-1,0,0);return best
out={'scope':'Exact bounded method controls only; no universal conclusion','small':[],'efficient_cubic':[],'cluster_controls':[]}
# Independent matching enumeration validates the branching recurrence.
for n in range(2,6):
 es=list(itertools.combinations(range(n),2));count=0
 for m in range(1<<len(es)):
  a=adj(n,[e for z,e in enumerate(es) if m>>z&1])
  if not connected(a):continue
  s=saturation(a);assert s==brute_s(a);i=indom(a);d=max(x.bit_count() for x in a)
  assert s<=(d*i+1)//2;count+=1
 out['small'].append(dict(n=n,connected_labeled=count))
# Cubic graphs with an efficient dominating set: arbitrary shuffled leaf cycles.
rng=random.Random(20261030)
for k in range(2,6):
 for trial in range(12):
  leaves=list(range(k,4*k));rng.shuffle(leaves)
  es=[(j,k+3*j+t) for j in range(k) for t in range(3)]
  es += list(zip(leaves,leaves[1:]+leaves[:1]));a=adj(4*k,es)
  assert connected(a) and all(x.bit_count()==3 for x in a)
  # n <= (Delta+1)i and the k centers dominate independently, so i=k exactly.
  s=saturation(a);out['efficient_cubic'].append(dict(k=k,trial=trial,s=s,bound=(3*k+1)//2,edges=es))
  assert s<=(3*k+1)//2
# Connected dense blocks expose parity costs without changing quantifiers.
for k in range(2,5):
 es=[]
 for j in range(k):es += [(4*j+u,4*j+v) for u,v in itertools.combinations(range(4),2) if (u,v)!=(0,1)]
 es += [(4*j+1,4*((j+1)%k)) for j in range(k)]
 a=adj(4*k,es);s=saturation(a);i=indom(a);d=max(x.bit_count() for x in a)
 out['cluster_controls'].append(dict(k=k,i=i,s=s,delta=d,bound=(d*i+1)//2))
# A connected quotient need not contain a matching covering half its vertices.
out['quotient_obstruction']={'graph':'K1,4','vertices':5,'matching_number':1,'ceil_half_vertices':3,'implication':'Connectivity alone cannot pair almost all domination cells.'}
(L/(sys.argv[1] if len(sys.argv)>1 else 'checks.json')).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:len(v) if isinstance(v,list) else v for k,v in out.items()},indent=2))
