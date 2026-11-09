import itertools
from fractions import Fraction
from math import lcm,prod,gcd
import pathlib,json
L=pathlib.Path(__file__).resolve().parents[1];out=[];a=[0,1]
for n in range(2,10):a.append(a[-1]*(a[-1]+1))
def tuples(m,rem,lo,cap):
 if m==1:
  if rem.numerator==1 and lo<=rem.denominator<=cap:yield (rem.denominator,)
  return
 hi=min(cap,(m*rem.denominator)//rem.numerator)
 for d in range(max(lo,(rem.denominator+rem.numerator-1)//rem.numerator),hi+1):
  r=rem-Fraction(1,d)
  if r>0:
   for t in tuples(m-1,r,d,cap):yield(d,)+t
for n,cap in [(4,1000000),(5,1000000),(6,1000000),(7,100),(8,40)]:
 count=cyclic=0;best=0;witness=None
 for target in range(1,n//2+1):
  for ds in tuples(n,Fraction(target),2,cap):
   count+=1;lc=lcm(*ds);order=prod(ds)//(lc*lc)
   # K + two copies Z/lcm: cyclic iff fourth-largest p-valuation is zero for every p
   if all(gcd(gcd(ds[i],ds[j]),gcd(ds[k],ds[h]))==1 for i,j,k,h in itertools.combinations(range(n),4)):
    cyclic+=1
    if order>best:best=order;witness=ds
 r=dict(n=n,denominator_cap=cap,sorted_tuples=count,cyclic=cyclic,best_order=best,conjectured=a[n-1],witness=witness,violation=best>a[n-1],scope='all di >= 2 within cap, integer reciprocal sum; labels di=1 reduce to smaller n');out.append(r);print(json.dumps(r),flush=True);(L/'outputs/star.json').write_text(json.dumps(out,indent=2))
