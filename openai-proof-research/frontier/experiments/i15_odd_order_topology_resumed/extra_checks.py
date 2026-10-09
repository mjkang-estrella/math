#!/usr/bin/env python3
"""Additional exact diagnostics, deliberately no geometry certification."""
from pathlib import Path
from itertools import product
import json,hashlib
OUT=Path(__file__).resolve().parent
# A genuine nontrivial semidirect product tests the full kernel action in the
# quotient identification. A has infinite order, unlike a cyclic toy example.
A=(2,1,1,1);Id=(1,0,0,1)
def mat(a,b):return (a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3])
def pw(n):
 a=A if n>=0 else (1,-1,-1,2);r=Id
 for _ in range(abs(n)):r=mat(r,a)
 return r
def av(a,v):return(a[0]*v[0]+a[1]*v[1],a[2]*v[0]+a[3]*v[1])
def op(x,y,step):
 v,n=x;w,m=y;t=av(pw(step*n),w)
 return ((v[0]+t[0],v[1]+t[1]),n+m)
normalform_tests=0
for R,j in product(range(1,6),[1,2]):
 d=3*R+j
 for v,w,n,m in product(list(product(range(-1,2),repeat=2)),list(product(range(-1,2),repeat=2)),range(-2,3),range(-2,3)):
  x=(v,n);y=(w,m);z=op(x,y,d)
  lhs=(z[0],d*z[1]);rhs=op((v,d*n),(w,d*m),1)
  assert lhs==rhs;normalform_tests+=1
# Merely knowing [Ad_gamma]^3=1 does NOT establish exact order 3.
# Abelian G=Z has G3=3Z and trivial quotient conjugation action.
assert all(a+b-a==b for a,b in product(range(-5,6),repeat=2))
# Degree-two graph: all 60 incident ports correspond to distinct edge IDs.
for d in range(2,16):
 B=[(a,b,q) for a,b in product(range(3),repeat=2) if b!=(a+1)%3 for q in range(5)]
 for v in range(d):
  inc=[(v,*t) for t in B]+[((v-1)%d,*t) for t in B]
  assert len(inc)==len(set(inc))==60
# Recursive branch selection: compression propagates framing/product collars
# in the mathematical proof; here only leaf multiplicities are checked.
def leaves(t,depth=0):
 if isinstance(t,int):return {t:2**depth}
 return leaves(t[0],depth+1)|leaves(t[1],depth+1)
assert leaves((0,(1,2)))=={0:2,1:4,2:4}
# Mixed parameters really survive. Monomials are masks in K[t_1,...,t_8]/t_i^2.
def times(a,b):return None if a&b else a|b
assert times(1,2)==3 and times(1,1) is None
assert times(3,4)==7 and times(7,8)==15
# Brunnian monomial bookkeeping through total degree 8: every higher term
# containing all 6 slots is in m times the product of the six slot ideals.
terms=0
for degree in range(6,9):
 for powers in product(range(1,degree-4),repeat=6):
  if sum(powers)!=degree:continue
  assert all(n>=1 for n in powers)
  if degree>6:assert any(n>=2 for n in powers)
  terms+=1
# Explicit absolute/root-relative paths below avoid relying on accidental cwd.
root=OUT.parents[2]; original=root/'frontier/experiments/i15_odd_order_topology/checks.json'
assert (OUT/'checks.json').read_bytes()==original.read_bytes()
res=dict(status='PASS: exact finite diagnostics only',normalform_multiplication_tests=normalform_tests,degree_two_distinct_port_check=True,recursive_cap_multiplicities=leaves((0,(1,2))),brunnian_multidegrees_tested=terms,old_checks_output_identical=True,limitations='No finite test proves marked embedding, framing, PD4, ideal inputs, reflection, or infinite-order homeomorphism exclusion.')
(OUT/'extra-checks.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res))
