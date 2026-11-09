"""Independent finite exact symbolic audit of the source recurrence and closed form.
Not a proof for all n. Recurrence copied from source Theorem 4.1 (4.1),(4.2).
"""
import sympy as s
from sympy.functions.combinatorial.numbers import stirling
from math import factorial
from pathlib import Path
import json
N=8
def complete(n, args):
 return sum(s.bell(n,k,args[:n-k+1]) for k in range(1,n+1))
xs=s.symbols('x1:'+str(N+1))
psi=[s.Integer(0)]
out=[]
for n in range(1,N+1):
 sigma=(-1)**n*complete(n,tuple(-factorial(j-1)*xs[j-1] for j in range(1,n+1)))
 big=s.Integer(0)
 for v in range(2,n+1):
  for k in range(min(v,n-v)+1):
   big+=(-1)**(v+1)*stirling(v+1,k+1,kind=1,signed=True)*s.ff(n,k)*s.bell(n-k,v,tuple(psi[1:n-k-v+2]))
 recursive=s.expand(n*psi[-1]+sigma+big)
 hs=[sum((-1)**(j+1)*xs[j-1]/j for j in range(1,i+1)) for i in range(1,n+1)]
 closed=s.expand(-complete(n,tuple(-factorial(i)*hs[i-1] for i in range(1,n+1))))
 assert s.expand(recursive-closed)==0,n
 poly=s.Poly(recursive,*xs)
 for mon,coef in poly.terms():
  d=sum(mon);w=sum((j+1)*a for j,a in enumerate(mon))
  z=s.prod((j+1)**a*factorial(a) for j,a in enumerate(mon))
  expected=(-1)**(w+1)*s.Rational(factorial(n),z)*s.binomial(n-w+d-1,d-1)
  assert coef==expected,(n,mon,coef,expected)
 assert len(poly.terms())==sum(s.partition(j) for j in range(1,n+1))
 if n>=2:
  if n%2==0:
   assert s.Poly(big,*xs).coeff_monomial(xs[0]**n)==-2
  else:
   assert s.Poly(big,*xs).coeff_monomial(xs[0]**(n-2)*xs[1])==n*(n-1)
 psi.append(recursive)
 out.append(dict(n=n,monomials=len(s.Poly(recursive,*xs).terms()),plus=str(recursive.subs(dict.fromkeys(xs,1))),minus=str(recursive.subs(dict.fromkeys(xs,-1))),identity=True,all_coefficients_match=True,full_partition_support=True))
 print(n,'PASS',flush=True)
Path(__file__).with_name('kellner-exact.json').write_text(json.dumps(dict(degree=N,results=out,scope='finite symbolic identity audit, no all-degree certification'),indent=2))
