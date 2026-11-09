import itertools,json,random,time
from small_graphs import graphs,iota
# importing isolation would run its experiment, so only copy the function block
from pathlib import Path
s=Path(__file__).with_name('isolation.py').read_text();exec(s[s.index('def product'):s.index('r=random.Random')])
def canon(a):
 n=len(a);groups={}
 for v in range(n):groups.setdefault(a[v].bit_count(),[]).append(v)
 perms=[list(itertools.permutations(groups[d])) for d in sorted(groups)]
 best=None
 for chunks in itertools.product(*perms):
  p=sum((list(c) for c in chunks),[]);b=tuple(sum(1<<j for j in range(n) if a[u]>>p[j]&1) for u in p)
  if best is None or b<best:best=b
 return best
pool={}
for n in range(2,7):
 for mask,a in graphs(n):
  z=iota(a)
  if z>=2:pool[canon(a)]=z
items=list(pool.items());count=0
for i,(a,z) in enumerate(items):
 for b,w in items[i:]:
  ans=below(product(a,b),z*w);count+=1
  if ans is not None:print(json.dumps(dict(counterexample=True,a=a,b=b,witness=ans)),flush=True);raise SystemExit
print(json.dumps(dict(stage='all_factors_to_6',canonical_hard_factors=len(items),pairs=count,counterexample=False)),flush=True)
r=random.Random(8903);extra=[]
for n in range(7,11):
 for t in range(40):
  prob=[.12,.2,.3,.4][t%4];a=[0]*n
  for u,v in itertools.combinations(range(n),2):
   if r.random()<prob:a[u]|=1<<v;a[v]|=1<<u
  z=iota(a)
  if z>=2:extra.append((a,z))
start=time.monotonic();count=0
for i,(a,z) in enumerate(extra):
 for b,w in items:
  ans=below(product(a,b),z*w);count+=1
  if ans is not None:print(json.dumps(dict(counterexample=True,a=a,b=b,witness=ans)),flush=True);raise SystemExit
  if time.monotonic()-start>100:break
 if time.monotonic()-start>100:break
print(json.dumps(dict(stage='seeded_extension',extra_factors=len(extra),pairs_completed=count,counterexample=False,seed=8903)),flush=True)
