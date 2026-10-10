"""Independent exact checks of ordering covers and the connected spectral example."""
from fractions import Fraction as F
from itertools import permutations,combinations
from math import factorial,comb,ceil
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
def ideals(n):
 if not n:return [0,1]
 old=ideals(n-1);return [a|(b<<(1<<(n-1))) for a in old for b in old if not b&~a]
def mass(good,n,p):return sum((p**s.bit_count()*(1-p)**(n-s.bit_count()) for s in good),F(0))
orders=0
for n in range(1,5):
 for d in ideals(n):
  if not d:continue
  good={s for s in range(1<<n) if d>>s&1}
  h=[s for s in range(1,1<<n) if s not in good and all(t in good for t in subs(s) if t!=s)]
  bad={s for s in range(1<<n) if not any(t in good and (s^t) in good for t in subs(s))}
  loops=[e for e in h if e.bit_count()==1];vertices=sum(loops);edges=[e for e in h if e&vertices==0 and e.bit_count()>=2]
  pairs=[(e,f) for e in edges for f in edges if (e&f).bit_count()==1];expected=F(0);p=F(1,3)
  for pi in permutations(range(n)):
   orders+=1;pos={v:i for i,v in enumerate(pi)};g=set(loops)
   for e,f in pairs:
    v=(e&f).bit_length()-1
    if all(pos[u]<pos[v] for u in range(n) if (e^(1<<v))>>u&1) and all(pos[u]>pos[v] for u in range(n) if (f^(1<<v))>>u&1):g.add(e|f)
   ck(all(any(i&s==i for i in g) for s in bad));expected+=sum((p**i.bit_count() for i in g),F(0))
  expected/=factorial(n)
  bound=sum((p for e in loops),F(0))+sum((F(factorial(e.bit_count()-1)*factorial(f.bit_count()-1),factorial((e|f).bit_count()))*p**(e|f).bit_count() for e,f in pairs),F(0))
  ck(expected<=bound)
# Exact triangle-book probabilities, core structure, and optimal cover.
books=[]
for m in range(1,8):
 n=m+2;p=F(1,7);edges=[3]+[(1<<j)|v for j in range(2,n) for v in [1,2]]
 good={s for s in range(1<<n) if not any(e&s==e for e in edges)}
 ck(mass(good,n,p)==(1-p)**2+2*p*(1-p)**(m+1))
 for s in range(1<<n):
  colorable=any(t in good and (s^t) in good for t in subs(s));ck(colorable==(not (s&3==3 and s>>2!=0)))
 books.append(dict(m=m,p=str(p),all_core_cost=str(m*p**3),optimal_cost=str(min(p*p,m*p**3))))
# Connected (r+1)-uniform example: complete core size 2r+1 and m petals of size r through core vertex zero.
spectral=[]
for r,m in [(1,1),(1,2),(2,1),(2,2),(3,1)]:
 core=(1<<(2*r+1))-1;petals=[((1<<r)-1)<<(2*r+1+i*r) for i in range(m)];n=2*r+1+r*m;p=F(1,8);C=F(2);a1=sum((F(comb(2*r,k))*p**k*(1-p)**(2*r-k) for k in range(r)),F(0))
 good={s for s in range(1<<n) if (s&core).bit_count()<=r and not any((s&(b|1))==(b|1) for b in petals)};a=mass(good,n,p)
 for s in range(1<<n):
  ck(any(t in good and (s^t) in good for t in subs(s))==(s&core!=core))
 def bcoef(u):
  outside=((1<<n)-1)^u
  return (1-p)**u.bit_count()*sum(((-1)**z.bit_count()*sum((p**y.bit_count()*(1-p)**(outside.bit_count()-y.bit_count()) for y in subs(outside) if (z|y) in good),F(0)) for z in subs(u)),F(0))
 energy=F(0);odd=F(0);pmask=sum(petals)
 for u in subs(pmask):
  if not u:continue
  predicted=p*a1
  for block in petals:
   k=(u&block).bit_count();predicted*=1-p**r if k==0 else (-1)**(k+1)*(1-p)**k*p**(r-k)
  b=bcoef(u);ck(b==predicted);ck(b*b<a*a)
  energy+=(C*p)**u.bit_count()*b*b
  if u.bit_count()%2:odd+=(C*p)**u.bit_count()*b*b
 B=p*p+C*p*(1-p)**2;Bm=p*p-C*p*(1-p)**2
 ck(energy==(p*a1)**2*((1-2*p**r+B**r)**m-(1-p**r)**(2*m)))
 ck(odd==(p*a1)**2*((1-2*p**r+B**r)**m-(1-2*p**r+Bm**r)**m)/2)
 spectral.append(dict(r=r,m=m,n=n,mass=str(a),petal_spectral_cost=str(energy/a**2),odd_cost=str(odd/a**2),optimal_integral_cost=str(p**(2*r+1))))
# Rational asymptotic control quantities; no enormous exponent evaluation.
limits=[]
for C in [F(101,100),F(3,2),F(2),F(25*512**4)]:
 p=min(F(1,8),1/(4*C),(1-1/C)/2);B=p*p+C*p*(1-p)**2;ck(0<p<B<1 and C*p<1)
 row=[]
 for r in [4,8,16,32,64]:
  M=ceil(r/B**r);badbound=2*p*(4*p)**r+M*p**(r+1);x=B**r-2*p**r
  ck(M*B**r>=r)
  row.append(dict(r=r,M=str(M),bad_probability_upper=str(badbound),log_growth_lower=str(M*x/2) if x>=0 else None))
 limits.append(dict(C=str(C),p=str(p),B=str(B),bounds=row))
# Actual downset with a fractional/integral budget gap, at low mass only.
from functools import lru_cache
p=F(5,13);cores=[sum(1<<i for i in c) for c in combinations(range(5),3)]
opts=[(sum(1<<i for i,c in enumerate(cores) if s&c==s),p**s.bit_count(),s) for s in range(32)];opts=[x for x in opts if x[0]];table={}
@lru_cache(None)
def dp(mask):
 if not mask:return F(0),()
 i=(mask&-mask).bit_length()-1
 result=min((v+dp(mask&~m)[0],(s,)+dp(mask&~m)[1]) for m,v,s in opts if m>>i&1)
 table[mask]=result;return result
opt,gen=dp(1023);dual=p*p/3
ck(opt==F(1150,2197));ck(10*dual==F(250,507)<F(1,2)<opt)
for mask,cost,ss in opts:ck(mask.bit_count()*dual<=cost)
gap=dict(n=5,p=str(p),downset='cardinality at most 1',mass=str((1-p)**5+5*p*(1-p)**4),integral=str(opt),generators=gen,fractional=str(10*dual),dual_mass_per_core=str(dual),dp_values={str(k):str(v[0]) for k,v in sorted(table.items())})
print(json.dumps(dict(status='PASS' ,assertions=checks,orderings=orders,actual_downset_gap=gap,books=books,spectral_examples=spectral,asymptotic_bounds=limits),indent=2))
