from math import factorial,prod
from fractions import Fraction
import json
A=(3,5,6,7,8,14,16,20,36)
B=(4,10,12,15,18,21,32)
assert len(set(A+B))==16 and min(A+B)>1 and len(A)!=len(B)
def fp(S):return prod((Fraction(factorial(t),t**t) for t in S),start=Fraction(1))
left,right=fp(A),fp(B)
assert left==right
# Independent cross multiplication, without rational reduction.
L=prod(factorial(a) for a in A)*prod(b**b for b in B)
R=prod(factorial(b) for b in B)*prod(a**a for a in A)
assert L==R
def v(n,p):
 k=0
 while n%p==0:k+=1;n//=p
 return k
primes=[p for p in range(2,37) if all(p%d for d in range(2,p))]
rows=[]
for p in primes:
 def E(S):return sum(sum(t//(p**j) for j in range(1,7))-t*v(t,p) for t in S)
 x,y=E(A),E(B);assert x==y
 rows.append({'p':p,'A':x,'B':y})
# Full 16 x 11 individual table, independently using factorization of t!.
table=[]
for t in sorted(A+B):
 row=[sum(v(j,p) for j in range(2,t+1))-t*v(t,p) for p in primes]
 table.append({'t':t,'side':'A' if t in A else 'B','valuations':row})
assert all(sum(r['valuations'][j]*(1 if r['side']=='A' else -1) for r in table)==0 for j in range(len(primes)))
print(json.dumps({'status':'PASS','A':A,'B':B,'common_numerator':left.numerator,'common_denominator':left.denominator,'cross_product_decimal_digits':len(str(L)),'prime_totals':rows,'primes':primes,'individual_table':table},indent=2))
