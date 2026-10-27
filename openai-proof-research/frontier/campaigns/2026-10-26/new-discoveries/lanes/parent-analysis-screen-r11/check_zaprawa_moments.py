"""Exact finite-measure checks; evidence only, universal proof is in proposal."""
from fractions import Fraction as F
import random,json
from pathlib import Path
Z=(F(0),F(0));O=(F(1),F(0))
def add(x,y):return(x[0]+y[0],x[1]+y[1])
def neg(x):return(-x[0],-x[1])
def sub(x,y):return add(x,neg(y))
def mul(x,y):return(x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def scale(a,x):return(a*x[0],a*x[1])
def power(x,n):
 y=O
 for _ in range(n):y=mul(y,x)
 return y
def normsq(x):return x[0]**2+x[1]**2
def total(xs):
 out=Z
 for x in xs:out=add(out,x)
 return out
pool=[O,neg(O),(F(0),F(1)),(F(0),F(-1)),(F(3,5),F(4,5)),(F(5,13),F(-12,13))]
assert all(normsq(z)==1 for z in pool)
rng=random.Random(20261027);checks=0;two_equalities=0
for trial in range(160):
 size=2 if trial<40 else rng.randrange(3,7)
 pts=rng.sample(pool,size);weights=[rng.randrange(1,20) for _ in pts];weights=[F(w,sum(weights)) for w in weights]
 moment=lambda n:total(scale(w,power(z,n)) for z,w in zip(pts,weights))
 rhs=1-normsq(moment(1));assert rhs>=0
 for n in range(1,15):
  det=sub(mul(moment(n-1),moment(n+1)),power(moment(n),2))
  sym=scale(F(1,2),total(scale(w*v,mul(power(mul(z,t),n-1),power(sub(z,t),2))) for z,w in zip(pts,weights) for t,v in zip(pts,weights)))
  assert det==sym
  assert normsq(det)<=rhs**2
  if size==2:assert normsq(det)==rhs**2;two_equalities+=1
  checks+=1
out={'status':'PASS','exact_finite_measure_cases':checks,'arbitrary_two_point_equalities':two_equalities,'universal_proof':'ZAPRAWA-PROPOSAL.md','formal_or_novelty_claim':False,'discovery_credit':0}
Path(__file__).with_name('zaprawa-exact-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
