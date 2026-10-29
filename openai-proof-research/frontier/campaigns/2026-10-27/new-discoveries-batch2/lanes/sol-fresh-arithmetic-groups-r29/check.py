#!/usr/bin/env python3
import os,resource,signal,json,math,itertools,functools
for v in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[v]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(45,45));signal.alarm(55)
@functools.lru_cache(None)
def parts(n,m=None):
 if not n:return ((),)
 if m is None:m=n
 return tuple((k,)+t for k in range(min(m,n),1-1,-1) for t in parts(n-k,k))
@functools.lru_cache(None)
def hooks(lam,k):
 # Beta numbers encode rim hooks: move a bead k places into an empty position.
 L=len(lam); b=tuple(lam[i]+L-i-1 for i in range(L));B=set(b);out=[]
 for x in b:
  if x>=k and x-k not in B:
   c=sorted(B-{x}|{x-k},reverse=True)
   mu=tuple(y-L+i+1 for i,y in enumerate(c));mu=tuple(t for t in mu if t)
   out.append((mu,(-1)**sum(x-k<z<x for z in b)))
 return tuple(out)
@functools.lru_cache(None)
def ch(lam,cyc):
 if not cyc:return int(not lam)
 return sum(s*ch(mu,cyc[1:]) for mu,s in hooks(lam,cyc[0]))
def support(x):
 s=set();p=2
 while p*p<=x:
  if x%p==0:
   s.add(p)
   while x%p==0:x//=p
  p+=1
 if x>1:s.add(x)
 return s
rows=[];total=0
for n in range(1,19):
 ps=parts(n);pr=[k for k in range(2,n+1) if support(k)=={k}];ix={p:i for i,p in enumerate(pr)}
 masks=[sum(1<<ix[p] for p in set().union(*(support(k) for k in cyc))) for cyc in ps]
 smallest=None
 alternating_min=None
 for lam in ps:
  bucket=[0]*(1<<len(pr))
  for cyc,mask in zip(ps,masks):bucket[mask]+=ch(lam,cyc)
  # Boolean zeta transform gives every prime-set multiplicity.
  for i in range(len(pr)):
   for mask in range(1<<len(pr)):
    if mask>>i&1:bucket[mask]+=bucket[mask^(1<<i)]
  for mask,v in enumerate(bucket):
   total+=1
   if smallest is None or v<smallest['multiplicity']:smallest=dict(partition=lam,primes=[p for p in pr if mask>>ix[p]&1],multiplicity=v)
   if v<0:
    print(json.dumps(dict(counterexample=dict(n=n,**smallest)),indent=2));raise SystemExit
 for lam in ps:
  bucket=[0]*(1<<len(pr))
  for cyc,mask in zip(ps,masks):
   if (n-len(cyc))%2==0:
    split=all(k%2 for k in cyc) and len(cyc)==len(set(cyc))
    bucket[mask]+=(1+split)*ch(lam,cyc)
  for i in range(len(pr)):
   for mask in range(1<<len(pr)):
    if mask>>i&1:bucket[mask]+=bucket[mask^(1<<i)]
  conjugate=tuple(sum(a>=i for a in lam) for i in range(1,lam[0]+1))
  for mask,v in enumerate(bucket):
   total+=1
   if n>=2 and lam==conjugate:assert v%2==0;v//=2
   if alternating_min is None or v<alternating_min['multiplicity']:
    alternating_min=dict(partition=lam,primes=[p for p in pr if mask>>ix[p]&1],multiplicity=v)
   if v<0:
    print(json.dumps(dict(counterexample=dict(group='alternating',n=n,**alternating_min)),indent=2));raise SystemExit
 # Full exact row orthogonality for n<=8 validates the character implementation.
 if n<=8:
  def z(c):return math.prod(k**c.count(k)*math.factorial(c.count(k)) for k in set(c))
  from fractions import Fraction
  for i,a in enumerate(ps):
   for j,b in enumerate(ps):
    assert sum(Fraction(ch(a,c)*ch(b,c),z(c)) for c in ps)==(i==j)
 rows.append(dict(n=n,partitions=len(ps),prime_sets=1<<len(pr),minimum=smallest,alternating_minimum=alternating_min))
 ch.cache_clear();hooks.cache_clear()
print(json.dumps(dict(status='no counterexample in stated finite scope',tests=total,rows=rows),indent=2))
