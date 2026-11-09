from pathlib import Path
from fractions import Fraction as F
from math import factorial
import json
L=Path(__file__).resolve().parent
def mul(p,q):
 r=[F(0)]*(len(p)+len(q)-1)
 for i,a in enumerate(p):
  for j,b in enumerate(q):r[i+j]+=a*b
 return r
def poly(roots):
 p=[F(1)]
 for r in roots:p=mul(p,[-F(r),F(1)])
 return p
def conv(p,q,n):
 r=[F(0)]*(n+1)
 for i,a in enumerate(p):
  for j,b in enumerate(q):
   if i+j>=n:r[i+j-n]+=a*b*F(factorial(i)*factorial(j),factorial(n)*factorial(i+j-n))
 return r
checks=[]
for n in range(2,8):
 p=poly(range(n));u=list(range(n-1))+[-sum(range(n-1))];q=poly(u)
 c=F(sum(t*t for t in u),2*n*(n-1))
 # Coefficient of epsilon^2: coefficient x^(n-2) of q times the convolution derivative weight.
 observed=[q[n-2]*p[i+2]*F((i+2)*(i+1),n*(n-1)) for i in range(n-1)]
 predicted=[-c*p[i+2]*(i+2)*(i+1) for i in range(n-1)]
 assert observed==predicted
 r=poly([2]*n);assert conv(conv(p,q,n),r,n)==conv(p,conv(q,r,n),n)
 checks.append(dict(n=n,centered_marks=u,c=str(c),second_order_identity=True,associativity_control=True))
for a,b,c in [(0,0,0),(1,2,3),(F(1,3),F(2,5),F(7,11))]:
 A,B,C=a*a,b*b,c*c;assert (A+C)*(B+C)-C*(A+B+C)==A*B
(L/'flow-exact-checks.json').write_text(json.dumps(dict(checks=checks,radicand_identity_controls=3,scope='Exact rational diagnostics; not an all-degree root inequality proof'),indent=2))
print('six coefficient/associativity controls and three rational radicand controls PASS')
