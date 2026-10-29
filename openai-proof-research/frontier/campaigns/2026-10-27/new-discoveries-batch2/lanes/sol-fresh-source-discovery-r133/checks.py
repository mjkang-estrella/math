from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
N=5; Z=(Q(0),)*N
E=[tuple(Q(i==j) for i in range(N)) for j in range(N)]
table={(0,1):E[2],(0,2):E[3],(1,2):E[4]}
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def neg(a):return tuple(-x for x in a)
def sub(a,b):return add(a,neg(b))
def scale(c,a):return tuple(c*x for x in a)
def br(a,b):
 v=Z
 for (i,j),w in table.items():v=add(v,scale(a[i]*b[j]-a[j]*b[i],w))
 return v
def D(x,y):return scale(Q(1,2),br(x,y))
def curvature(x,y,z):return sub(sub(D(x,D(y,z)),D(y,D(x,z))),D(br(x,y),z))
triples=0
for x,y,z in product(E,repeat=3):
 assert add(add(br(x,br(y,z)),br(y,br(z,x))),br(z,br(x,y)))==Z
 assert curvature(x,y,z)==scale(Q(-1,4),br(br(x,y),z))
 triples+=1
w=curvature(E[0],E[1],E[0]);assert w==scale(Q(1,4),E[3])
# This is g=n and L=0: PA1-PA3 hold identically; g is NOT perfect.
# It falsifies the universal flattening shortcut only, not a source conjecture.
lower=[set(range(5))]
for k in range(3):
 support=set()
 for i,j in product(range(5),lower[-1]):
  support.update(k for k,c in enumerate(br(E[i],E[j])) if c)
 lower.append(support)
assert lower==[set(range(5)),{2,3,4},{3,4},set()]
r=dict(status='PASS',exact_basis_triples=triples,lower_central_dimensions=[len(s) for s in lower],curvature_witness=[str(c) for c in w],scope='Known free class-three algebra; no perfect-g witness; no source resolution; rational diagnostic and shortcut obstruction only')
Path(__file__).with_name('check-results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
