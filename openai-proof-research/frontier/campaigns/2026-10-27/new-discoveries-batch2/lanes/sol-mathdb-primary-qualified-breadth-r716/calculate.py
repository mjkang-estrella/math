exec(open(__file__.replace('calculate.py','bind.py')).read().split('refs={}')[0])
from itertools import product
# Exact Gaussian-ring modular exponentiation, no floating point.
def mul(a,b,p):return ((a[0]*b[0]-a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
def power(a,k,p):
 b=(1,0)
 while k:
  if k&1:b=mul(b,a,p)
  a=mul(a,a,p);k//=2
 return b
p=19;k=360;s=[0,0];terms=0
for n in range(1,p):
 for m in range(1,p):
  den=(n*n+m*m)%p
  if not den:continue
  inv=(n*pow(den,-1,p)%p,-m*pow(den,-1,p)%p);v=power(inv,k,p)
  s=[(s[z]+v[z])%p for z in [0,1]];terms+=1
assert s==[1,0] and terms==324
exception_primes=[3,5,7,11,13,19,23,29,31,37,41,43,61,67,71,73,79,127,151,211]
w=[]
for p in exception_primes:
 squares={x*x%p for x in range(1,p)}
 for g in range(1,p):
  order=next(t for t in range(1,p) if pow(g,t,p)==1)
  if order==p-1 and (g*g+4)%p not in squares and (g*g+4)%p!=0:w.append({'p':p,'g':g,'g_order':order,'value':(g*g+4)%p});break
 else:raise AssertionError(p)
# Finite coordinate interpretation of fusion, not a general sigma-set theorem.
A={('a',i) for i in range(2)};bp={('b',i) for i in range(2)};bm={('minus',i) for i in range(2)}
def subs(S):
 v=list(S);return [frozenset(v[i] for i in range(len(v)) if mask>>i&1) for mask in range(1<<len(v))]
out=set()
for X in subs(A|bp):
 for Y in subs(A|bm):
  out.add(frozenset((X|Y)-{v for v in X|Y if (v[0]=='b' and ('minus',v[1]) in Y) or (v[0]=='minus' and ('b',v[1]) in X)}))
assert len(out)==36
write('calculations.json',{'gaussian':{'p':19,'k':360,'modulus':19,'terms':324,'sum':s,'meaning':'literal fails mod p; source already flags p-versus-k correction; zero credit'},'generator_exception_witnesses':w,'fusion_finite_coordinate_model':{'a':2,'b':2,'count':len(out),'expected':36,'meaning':'routine finite instance, no full-scope claim'}})
print('PASS exact Gaussian check;20 exceptional-prime witnesses;finite fusion count36')
