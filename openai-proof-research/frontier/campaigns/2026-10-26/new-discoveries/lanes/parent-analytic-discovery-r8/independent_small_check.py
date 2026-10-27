from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json
from shifted_content_check import compute
# Independent scalar series multiplication / long-log differentiation, no Stirling or cumulant recurrence.
def mul(a,b,N):
 c=[0j]*(N+1)
 for i in range(N+1):
  for j in range(N+1-i):c[i+j]+=a[i]*b[j]
 return c
# Gaussian rationals represented exactly as Python complex-like Sympy I expressions.
import sympy as s
I=s.I;N=7;rows=[]
import contextlib,io
with contextlib.redirect_stdout(io.StringIO()): _,B=compute(N,return_cumulants=True)
for u,v in [(2,3),(0,1),(7,-2)]:
 f=[s.Integer(0)]*(N+1);f[0]=s.Integer(1)
 for m in range(1,N+1):
  cm=0
  for l in range(m+1):
   al=s.prod(u-j*(j+1) for j in range(l))/(2**l*s.factorial(l))
   ar=s.prod(v-j*(j+1) for j in range(m-l))/(2**(m-l)*s.factorial(m-l))
   cm+=al*ar*(1+I)**l*(1-I)**(m-l)
  den=[s.Integer(1)]+[s.Integer(0)]*N
  for j in range(1,m+1):
   den=[s.expand(sum(den[k]*j**(n-k) for k in range(n+1))) for n in range(N+1)]
  for n in range(m,N+1):f[n]+=s.expand(cm*den[n-m])
 # F'/F=log(F)' via exact series division, followed by integration.
 q=[]
 for n in range(N):q.append(s.expand((n+1)*f[n+1]-sum(f[k]*q[n-k] for k in range(1,n+1))))
 vals=[str(s.simplify(s.im(q[n-1]/n)/2**n)) for n in [1,3,5,7]]
 expected=[str(s.Rational(sum(y*u**a*v**b for (a,b),(x,y) in B[n].items()),2**(2*n)*factorial(n))) for n in [1,3,5,7]]
 assert vals==expected,(vals,expected)
 rows.append({'u':u,'v':v,'literal_kappa_r1_r4':vals,'agrees_with_integer_cumulant_path':True})
print(json.dumps(rows,indent=2));Path('independent-small-check.json').write_text(json.dumps(rows,indent=2)+'\n')
