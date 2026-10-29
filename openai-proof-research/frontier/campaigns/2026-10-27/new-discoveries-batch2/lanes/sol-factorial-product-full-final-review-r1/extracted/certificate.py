from pathlib import Path
from fractions import Fraction
from math import factorial,prod
import json
R=Path(__file__).resolve().parent
A=[3,5,6,7,8,14,16,20,36]; B=[4,10,12,15,18,21,32]
primes=[p for p in range(2,37) if all(p%d for d in range(2,p))]
def vp(n,p):
 k=0
 while n%p==0:n//=p;k+=1
 return k
def entry(t,p):
 q=p;s=0
 while q<=t:s+=t//q;q*=p
 v=s-t*vp(t,p)
 assert v==vp(factorial(t),p)-vp(t**t,p)
 return v
matrix=[[entry(t,p) for p in primes] for t in A+B]
totals=[[sum(entry(t,p) for t in S) for p in primes] for S in [A,B]]
assert totals[0]==totals[1]==[-123,-37,-4,-8,6,5,3,2,1,1,1]
assert len(set(A+B))==16 and min(A+B)>1
products=[prod(Fraction(factorial(t),t**t) for t in S) for S in [A,B]]
assert products[0]==products[1]
assert prod(factorial(t) for t in A)*prod(t**t for t in B)==prod(factorial(t) for t in B)*prod(t**t for t in A)
out={'status':'EXACT_PASS','A':A,'B':B,'primes':primes,'rows':matrix,'totals':totals,
 'common_numerator':products[0].numerator,'common_denominator':products[0].denominator,
 'individual_valuations_checked_two_ways':176}
(R/'certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print('exact rational, integer and 176 valuation checks PASS')
