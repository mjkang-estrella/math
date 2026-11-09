from pathlib import Path
from itertools import product,permutations
import json
D=Path(__file__).resolve().parents[1]
Q=range(16)
def f(x,y):
 a,b,c=[(x>>i)&1 for i in range(3)];d,e,g=[(y>>i)&1 for i in range(3)]
 return (a*b*g)^(a*e*c)^(d*b*c)
def mul(x,y):return x^y^(f(x,y)<<3)
def grp(x,y):return x^y
def assoc(m,x,y,z):
 a=m(x,m(y,z));b=m(m(x,y),z)
 return next(w for w in Q if m(a,w)==b)
r={}
for name,m in [('group',grp),('loop',mul)]:
 assert all(m(x,0)==m(0,x)==x for x in Q)
 assert all(len({m(a,x) for x in Q})==16 and len({m(x,a) for x in Q})==16 for a in Q)
 assert all(m(m(m(x,y),x),z)==m(x,m(y,m(x,z))) for x,y,z in product(Q,repeat=3))
 vals=[assoc(m,*t) for t in product(Q,repeat=3)]
 r[name]={'associator_values':sorted(set(vals)),'nonzero_associators':sum(v!=0 for v in vals),'nucleus':[x for x in Q if all(assoc(m,x,y,z)==0 for y,z in product(Q,repeat=2))]}
 for x,y,z in product(Q,repeat=3):
  assert assoc(m,x,y,z)==(m(m(x,y),z)^m(x,m(y,z)))
 assert all(m(m(x,y),z)==m(x,m(y,z)) for x,y,z in product(Q,repeat=3)) == (name=='group')
r['distance']=sum(mul(x,y)!=grp(x,y) for x,y in product(Q,repeat=2));assert r['distance']==64
r['basis_associator']=assoc(mul,1,2,4);assert r['basis_associator']==8
r['factor_row_weights']=[sum(f(x,y) for y in range(8)) for x in range(8)]
# Negative controls: no cubic perturbation is associative and distance zero; a single-cell edit breaks Latin property.
assert all(grp(grp(x,y),z)==grp(x,grp(y,z)) for x,y,z in product(Q,repeat=3))
bad=[[mul(x,y) for y in Q] for x in Q];bad[1][2]^=8
assert len(set(bad[1]))<16
r['negative_controls']='PASS';r['source_inequivalence']='image cardinalities 1 and 2 are invariant under any bijective simultaneous relabeling; does not require identity preservation'
(D/'logs/exact.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
