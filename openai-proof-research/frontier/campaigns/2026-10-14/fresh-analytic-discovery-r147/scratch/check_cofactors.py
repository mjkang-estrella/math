"""Bounded exact algebra diagnostics; not a PDE or mathematical gate."""
from fractions import Fraction as F
from pathlib import Path
import json
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r147')
def eye(n):return [[F(i==j) for j in range(n)] for i in range(n)]
def trans(a):return list(map(list,zip(*a)))
def mul(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def add(a,b):return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def det(a):
 if not a:return F(1)
 return sum((-1)**j*a[0][j]*det([r[:j]+r[j+1:] for r in a[1:]]) for j in range(len(a)))
def adj(a):
 n=len(a);return [[(-1)**(i+j)*det([r[:i]+r[i+1:] for k,r in enumerate(a) if k!=j]) for j in range(n)] for i in range(n)]
def diag(xs):return [[F(xs[i]) if i==j else F(0) for j in range(len(xs))] for i in range(len(xs))]
def zero(a):return all(x==0 for row in a for x in row)
checks=[]
for n in [2,3,4]:
 for k in [1,2,3]:
  S=eye(n)
  for i in range(n-1):S[i][i+1]=F(k+i)
  P=mul(trans(S),mul(diag([0]+list(range(1,n))),S))
  # Different congruence inside the common-kernel complement, so no commutation assumption.
  R0=eye(n)
  if n>2:R0[1][2]=F(k)
  Q=mul(trans(S),mul(mul(trans(R0),mul(diag([0]+[2+i for i in range(n-1)]),R0)),S))
  assert det(add(P,Q))==0 and zero(mul(Q,adj(P)))
  U=eye(n);V=eye(n);U[-1][0]=F(k);V[0][-1]=F(k+1)
  A=mul(U,P);B=mul(V,Q)
  assert zero(mul(B,adj(A)))
  assert adj(mul(U,P))==mul(adj(P),adj(U))
  checks.append({'n':n,'shear':k,'common_kernel_cancellation':True,'factor_order':True})
# These are NOT transport counterexamples: they separate hypotheses of the algebra step.
P=diag([0,1]);Q=diag([1,0]);assert det(P)==det(Q)==0 and det(add(P,Q))==1 and not zero(mul(Q,adj(P)))
Qbad=diag([1,-1]);assert det(add(P,Qbad))==0 and not zero(mul(Qbad,adj(P)))
# Exact component convention: B adj(A) is the composite density, not adj(A) B.
A=[[F(1),F(2)],[F(3),F(7)]];B=[[F(2),F(1)],[F(0),F(3)]]
assert mul(B,adj(A))!=mul(adj(A),B)
res={'cases':checks,'negative_controls':['two singular PSD matrices with nonsingular sum','singular sum but indefinite Q','noncommuting composite factor order'],'scope':'finite rational algebra only; no source truth, PDE, Sobolev, contribution or acceptance gate'}
(R/'DIAGNOSTIC.json').write_text(json.dumps(res,indent=2)+'\n');print('9 exact matrix cases and 3 hypothesis/order diagnostics completed')
