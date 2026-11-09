#!/usr/bin/env python3
"""MIT. Exact algebra diagnostics only; not a mathematical or contribution gate."""
from fractions import Fraction as F
import json

def dot(a,b): return sum((x*y for x,y in zip(a,b)),F(0))
def mv(a,b): return [dot(row,b) for row in a]
def mm(a,b):return [[sum(a[i][k]*b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
def add(a,b):return [[a[i][j]+b[i][j] for j in range(3)] for i in range(3)]
J=[[F(-9,2),F(9,2),F(0)],[F(7,2),F(-27,2),F(147,11)],[F(44,7),F(132,49),F(-12)]]
v=[F(1),F(1),F(110,147)];ell=[F(14,25),F(6,25),F(147,550)]
assert mv(J,v)==[0,0,0]
assert [dot(ell,col) for col in zip(*J)]==[0,0,0]
assert dot(ell,v)==1
I15=[[F(15 if i==j else 0) for j in range(3)] for i in range(3)]
assert mm(J,mm(add(J,I15),add(J,I15)))==[[0]*3 for _ in range(3)]
Q=[F(0),F(20,7),F(-2530,3087)]
assert dot(ell,Q)==F(7,15)
assert F(7,2)*v[2]+F(33,7)*v[1]==F(22,3)
# Bivariate polynomial ring Q[lambda,L], using sparse exponent dictionaries.
def plus(*ps):
 d={}
 for p in ps:
  for k,x in p.items(): d[k]=d.get(k,F(0))+x
 return {k:v for k,v in d.items() if v}
def scale(p,c):return {k:x*c for k,x in p.items() if x*c}
def mul(p,q):
 d={}
 for (i,j),x in p.items():
  for (k,l),y in q.items():d[(i+k,j+l)]=d.get((i+k,j+l),F(0))+x*y
 return {k:v for k,v in d.items() if v}
a={(2,0):F(4),(1,0):F(144),(0,0):F(504),(0,1):F(-14)}
b={(2,0):F(4),(1,0):F(-24),(0,1):F(-14)}
c={(2,0):F(5040),(1,0):F(12096),(0,1):F(3528)}
det=plus(mul(a,b),c)
t={(2,0):F(2),(1,0):F(30),(0,1):F(-7)}
assert det==scale(plus(mul(t,t),{(0,1):F(-882)}),F(4))
for L,roots in [(0,[0,0,-15,-15]),(18,[0,-15,6,-21])]:
 p={(0,0):F(16)}
 for r in roots:p=mul(p,{(1,0):F(1),(0,0):F(-r)})
 reduced={}
 for (i,j),x in det.items():reduced[(i,0)]=reduced.get((i,0),F(0))+x*L**j
 reduced={k:x for k,x in reduced.items() if x}
 assert p==reduced
p=scale(mul({(2,0):F(1),(1,0):F(15),(0,0):F(14)},{(2,0):F(1),(1,0):F(15),(0,0):F(-70)}),F(16))
reduced={}
for (i,j),x in det.items():reduced[(i,0)]=reduced.get((i,0),F(0))+x*8**j
assert p=={k:x for k,x in reduced.items() if x}
assert F(-15,7)-F(12,11)*F(110,7)==F(-135,7)
print(json.dumps({'exact_algebra':'verified','jacobian_spectrum':[0,-15,-15],'center_coefficient':'7/15','indicial_polynomial':'4*((2*lambda*(lambda+15)-7*L)**2-882*L)/3969','mathematical_gate':None,'contribution_rating':None},sort_keys=True))
