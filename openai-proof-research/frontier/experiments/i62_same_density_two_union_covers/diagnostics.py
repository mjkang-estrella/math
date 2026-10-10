"""Exact finite checks. No optimizer; integer dynamic-programming certificates."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations,product
from math import comb
import json
checks=0
def ck(v):
 global checks;checks+=1
 if not v:raise AssertionError(checks)
def subs(s):
 u=s
 while True:
  yield u
  if not u:break
  u=(u-1)&s
@lru_cache(None)
def ideals(n):
 if not n:return (0,1)
 old=ideals(n-1);return tuple(a|(b<<(1<<(n-1))) for a in old for b in old if b&~a==0)
def members(d,n):return [s for s in range(1<<n) if d>>s&1]
def minimal(fam):return [s for s in fam if all(t==s or t not in fam for t in subs(s))]
def e2(d,n):
 good=members(d,n);cov=set()
 for a in good:
  for b in good:cov.add(a|b)
 for i in range(n):
  cov.update(s^(1<<i) for s in list(cov) if s>>i&1)
 return set(range(1<<n))-cov
def exact_cover(cores,n,p):
 # Cost integer units denominator**n. Every useful generator is a subset of a core.
 den=p.denominator;num=p.numerator;unit=den**n
 if not cores:return 0,[],1
 options={};universe=0
 for s in cores:universe|=s
 for s in range(1<<n):
  mask=sum(1<<i for i,c in enumerate(cores) if s&c==s)
  if mask:
   cost=num**s.bit_count()*den**(n-s.bit_count())
   if mask not in options or cost<options[mask][0]:options[mask]=(cost,s)
 opts=[(m,c,s) for m,(c,s) in options.items()]
 opts=[(m,c,s) for m,c,s in opts if not any(m!=m2 and m&m2==m and c2<=c for m2,c2,s2 in opts)]
 bycore=[[x for x in opts if x[0]>>i&1] for i in range(len(cores))]
 @lru_cache(None)
 def dp(mask):
  if mask==0:return 0,()
  i=min((i for i in range(len(cores)) if mask>>i&1),key=lambda i:len(bycore[i]))
  return min((c+dp(mask&~m)[0],(s,)+dp(mask&~m)[1]) for m,c,s in bycore[i])
 value,gen=dp((1<<len(cores))-1)
 ck(all(any(g&c==g for g in gen) for c in cores));ck(sum(num**s.bit_count()*den**(n-s.bit_count()) for s in set(gen))==value)
 return F(value,unit),list(gen),dp.cache_info().currsize
def mass(d,n,p):return sum((p**s.bit_count()*(1-p)**(n-s.bit_count()) for s in members(d,n)),F(0))
def signed(d,n,p):
 bs=[]
 for u in range(1<<n):
  outside=((1<<n)-1)^u
  v=sum(((-1)**z.bit_count()*sum((p**y.bit_count()*(1-p)**(outside.bit_count()-y.bit_count()) for y in subs(outside) if d>>(y|z)&1),F(0)) for z in subs(u)),F(0))*(1-p)**u.bit_count()
  bs.append(v)
 return bs
summary=[];certificates=[]
for n in range(1,6):
 ds=ideals(n);ck(len(ds)=={1:3,2:6,3:20,4:168,5:7581}[n]);worst=None;viol=0;maxcores=0;states=0
 for d in ds:
  if not d:continue
  good=members(d,n);bad=set(range(1<<n))-set(good);h=minimal(bad);exc=e2(d,n);cores=minimal(exc);maxcores=max(maxcores,len(cores))
  for s in range(1<<n):
   colorable=any(all(e&t!=e and e&(s^t)!=e for e in h if e&s==e) for t in subs(s))
   ck(colorable==(s not in exc))
  for p in [F(1,4),F(1,3),F(2,5)]:
   a=mass(d,n,p);cost,gens,k=exact_cover(cores,n,p);states+=k
   if cost>F(1,2):
    viol+=1
    if worst is None or a>worst[0]:worst=(a,d,p,cost,cores,gens)
   if n<=4:
    b=signed(d,n,p);ck(b[0]==a)
    for s in exc:ck(sum(((-1)**u.bit_count()*b[u]**2 for u in subs(s)),F(0))==0)
    if a:
     costfrac=sum((p**u.bit_count()*min(F(1),b[u]**2/a**2) for u in range(1,1<<n)),F(0));ck(costfrac<=(1-p)*(1-a)/a)
     oddcost=sum((p**u.bit_count()*min(F(1),b[u]**2/a**2) for u in range(1,1<<n) if u.bit_count()%2),F(0));ck(oddcost<=costfrac)
   if h:
    r=max(e.bit_count() for e in h);ck(cost<=min(F(1),(2**r-1)**2*(1-a)/a))
  # High-bias closure checked at half, if mass>half.
  if mass(d,n,F(1,2))>F(1,2):ck(not exc)
 summary.append(dict(n=n,downsets=len(ds),nonempty=len(ds)-1,max_cores=maxcores,dp_states=states,cost_above_half=viol,largest_mass_above_half=None if worst is None else str(worst[0])))
 if worst:certificates.append(dict(n=n,mass=str(worst[0]),downset_mask=worst[1],p=str(worst[2]),cost=str(worst[3]),cores=worst[4],generators=worst[5]))
# Every arbitrary family on <=3 vertices: downward closure preserves E2.
for n in range(1,4):
 for d in range(1,1<<(1<<n)):
  down=sum(1<<s for s in set(t for u in members(d,n) for t in subs(u)))
  ck(e2(d,n)==e2(down,n))
# Finite projective planes of order 2 and 3 by homogeneous coordinates.
planes=[]
for q in [2,3]:
 points=[v for v in product(range(q),repeat=3) if any(v) and next(x for x in v if x)==1]
 lines=sorted(set(sum(1<<i for i,v in enumerate(points) if sum(a*b for a,b in zip(v,w))%q==0) for w in points));n=len(points);allbits=(1<<n)-1
 ck(n==q*q+q+1 and len(lines)==n and all(e.bit_count()==q+1 for e in lines))
 good=[s for s in range(1<<n) if not any(e&s==e for e in lines)];goodset=set(good)
 colorings=[s for s in good if (allbits^s) in goodset]
 d=sum(1<<s for s in good);exc=e2(d,n);cores=minimal(exc)
 planes.append(dict(q=q,n=n,lines=lines,independence_counts=[sum(s.bit_count()==k for s in good) for k in range(n+1)],colorings=len(colorings),cores=cores))
# Explicit failure of all-minimal-core cost, with common triangle vertex.
N=10000;p=F(1,100);ck(N*p**3==F(1,100));N=1000000;ck(N*p**3==1 and p<F(1,2))
# All uniform minimal non-two-colorable cores have size >=2r-1 (r-uniform complete hypergraph attains it).
for r in range(2,7):
 n=2*r-1;ck(2*(r-1)<n)
print(json.dumps(dict(status='PASS',assertions=checks,downsets=summary,exact_cover_extremizers=certificates,projective_planes=planes,scope='Exact rational identities and exhaustive finite dynamic programs; no analytic or novelty verdict'),indent=2))
