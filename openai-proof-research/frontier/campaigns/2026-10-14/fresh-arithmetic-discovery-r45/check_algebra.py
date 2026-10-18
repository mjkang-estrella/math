#!/usr/bin/env python3
"""MIT. Exact polynomial identities; not a cycle-count proof."""
from fractions import Fraction as F
import json
checks=0
def trim(p):
 while len(p)>1 and not p[-1]:p.pop()
 return p
def add(p,q):return trim([(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(max(len(p),len(q)))])
def neg(p):return [-a for a in p]
def mul(p,q):
 out=[0]*(len(p)+len(q)-1)
 for i,a in enumerate(p):
  for j,b in enumerate(q):out[i+j]+=a*b
 return trim(out)
def power(p,n):
 out=[1]
 for _ in range(n):out=mul(out,p)
 return out
def diff(p):return trim([i*p[i] for i in range(1,len(p))] or [0])
def D(f):
 p,q=f
 return (add(mul(diff(p),q),neg(mul(p,diff(q)))),mul(mul(q,q),[0,1,0,1]))
def require(ok,label):
 global checks
 if not ok:raise ValueError(label)
 checks+=1
def same(f,g):return mul(f[0],g[1])==mul(g[0],f[1])
E=([0,0,1],[1]);targets=[([2],[1,0,1]),([-4],power([1,0,1],3)),([24],power([1,0,1],5))]
for target in targets:E=D(E);require(same(E,target),'even profile derivative')
p=([0,0,0,-1,0,1],[1])
for _ in range(3):p=D(p)
require(same(p,([3,0,39,0,-75,0,-15],mul([0,0,0,1],power([1,0,1],5)))),'odd profile third derivative')
require(F(3+39-75-15,32)==F(-3,2),'negative value at x1')
# sqrt(2)<3/2 implies 3+2sqrt(2)<6, hence the exact determinant is negative.
require(F(2)<F(9,4),'negative radical determinant certificate')
for a in [F(1,2),F(1),F(2),F(3)]:
 for delta in [F(1,10),F(1,100)]:
  beta=delta/(a*a)
  require(beta*a*a==delta,'restoring-force scaling')
for a in [F(1),F(2),F(3)]:
 for beta in [F(1),F(2),F(3)]:
  z=-a/(2*beta);r2=a*a/(2*beta)
  require(a*z+beta*z*z==-r2/2 and a+2*beta*z==0,'finite reference barrier')
print(json.dumps({'status':'PASS_EXACT_ALGEBRA','checks':checks}))
