#!/usr/bin/env python3
import os,resource
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(45,45))
import sympy as s,json
from pathlib import Path
x=s.Symbol('x')
def ev(t):
 if t is None:return s.Poly(x,x),[s.Poly(1,x)]
 a,wa=ev(t[0]);b,wb=ev(t[1]);return a*a+b*b*b,[2*a*w for w in wa]+[3*b*b*w for w in wb]
pair=(None,None);A=(pair,pair);B=(pair,None);t=(A,B)
a,wa=ev(A);b,wb=ev(B);p,w=ev(t);g=s.gcd(a,b*b);u=b*b//g;v=a//g
assert a*u==b*b*v
assert u.degree()<=a.degree()-1 and v.degree()<=b.degree()-1
M=s.Matrix([[q.nth(i) for q in w] for i in range(p.degree())]);rows=list(M.T.rref()[1]);det=M[rows,:].det();assert det!=0
ua=s.Matrix([[q.nth(i) for q in wa] for i in range(a.degree())]);target=s.Matrix([u.nth(i) for i in range(a.degree())]);assert ua.row_join(target).rank()>ua.rank()
checks=0
for m in range(4,202,2):
 for n in range(32,101):
  z=pow(m-1,n)-1;r=z;k=0
  while r%m==0:r//=m;k+=1
  assert m**(2*k)<=z
  assert k<=1+n.bit_length()-1
  checks+=1
out=dict(root_polynomial=str(p.as_expr()),A=str(a.as_expr()),B=str(b.as_expr()),gcd=str(g.as_expr()),U=str(u.as_expr()),V=str(v.as_expr()),intersection_identity=True,gradient_rank=M.rank(),minor_rows=rows,minor_determinant=str(det),U_in_actual_left_span=False,companion_cases=checks,companion_bound='N=32',scope='exact route obstruction and finite diagnostics; not full Conjecture3')
Path(__file__).with_name('exact-checks.json').write_text(json.dumps(out,indent=2));print(out)
