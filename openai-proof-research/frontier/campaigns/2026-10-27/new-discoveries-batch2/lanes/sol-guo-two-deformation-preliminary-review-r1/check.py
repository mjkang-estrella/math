from pathlib import Path
import json,math
from fractions import Fraction as F
import sympy as s
L=Path(__file__).resolve().parent
x=s.Symbol('x')
rows=[]
for n in [4,7,13,16,22,25,31,34,40,49]:
 phi=s.Poly(s.cyclotomic_poly(n,x),x);mod=phi**2
 m=list(reversed([int(c) for c in mod.all_coeffs()]));d=len(m)-1
 def red(a):
  a=list(a)
  for i in range(len(a)-1,d-1,-1):
   c=a[i]
   if c:
    for k in range(d):a[i-d+k]-=c*m[k]
  return (a+[0]*d)[:d]
 one=red([1]);zero=[0]*d
 def add(a,b):return [v+w for v,w in zip(a,b)]
 def mul(a,b):
  c=[0]*(2*d-1)
  for i,v in enumerate(a):
   if v:
    for j,w in enumerate(b):c[i+j]+=v*w
  return red(c)
 q=red([0,1]);qi=red([-v for v in m[1:]]) # q inverse since m[0]=1
 assert mul(q,qi)==one
 def power(a,e):
  out=one
  while e:
   if e&1:out=mul(out,a)
   a=mul(a,a);e//=2
  return out
 cache={}
 def qp(e):
  if e not in cache:cache[e]=power(q if e>=0 else qi,abs(e))
  return cache[e]
 def factor(e):return [a-b for a,b in zip(one,qp(e))]
 den=[one]
 for j in range(1,n):den.append(mul(den[-1],power(factor(9*j),3)))
 suffix=[one for _ in range(n)]
 for j in range(n-2,-1,-1):suffix[j]=mul(suffix[j+1],power(factor(9*(j+1)),3))
 def numerator(c):
  top=one;out=zero
  for j in range(n):
   out=add(out,mul(mul(top,qp(9*j)),suffix[j]))
   for b in [1+c*n,2-c*n,6]:top=mul(top,factor(b+9*j))
  return out
 t1,t2=(7,5) if n%9==4 else (4,8)
 l1,l2=(t1*n-1)//9,(t2*n-2)//9
 assert 0<l1<n and 0<l2<n
 assert s.gcd(phi,s.Poly(sum(v*x**i for i,v in enumerate(den[-1])),x)).degree()==0
 tests={str(c):numerator(c)==zero for c in [0,-t1,t2]};assert all(tests.values())
 def poch(e,k):
  out=F(1)
  for i in range(k):out*=1-F(2)**(e+9*i)
  return out
 exact=[]
 for c,ell,b in [(-t1,l1,7-t1*n),(t2,l2,8-t2*n)]:
  lhs=sum((poch(1+c*n,j)*poch(2-c*n,j)*poch(6,j)*F(2)**(9*j)/poch(9,j)**3 for j in range(ell+1)),F(0))
  rhs=poch(b,ell)*poch(3,ell)/(poch(9,ell)*poch(-9*ell,ell))
  assert lhs==rhs;exact.append(True)
 rows.append(dict(n=n,composite=not s.isprime(n),degree=d,L=[l1,l2],cleared_numerator_zero=tests,denominator_unit=True,q2_exact_identity=exact))
# Symbolic affine bounds: nonnegative coefficient and strictly positive constant
bounds=[]
for residue,t1,t2,L1,L2,J3,J7,J8 in [(4,7,5,(7,3),(5,2),(3,1),(4,1),(2,0)),(7,4,8,(4,3),(8,6),(3,2),(1,0),(5,3))]:
 for A,B,name in [(L1,J3,'L1-J3'),(L1,J7,'L1-J7'),(L2,J3,'L2-J3'),(L2,J8,'L2-J8'),((9,residue),L1,'n-L1'),((9,residue),L2,'n-L2')]:
  pair=[A[i]-B[i] for i in range(2)];assert pair[0]>=0 and pair[1]>0
  bounds.append(dict(residue=residue,inequality=name,affine=pair))
(L/'checker-evidence.json').write_text(json.dumps(dict(method='Independent integer common-denominator numerator arithmetic modulo monic Phi_n^2; rational q=2 identity checks; finite tests are not proof',cases=rows,uniform_affine_bounds=bounds),indent=2)+'\n')
print('PASS',len(rows),'exact ring cases, two rational identities each,',len(bounds),'uniform affine bounds')
