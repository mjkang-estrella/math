"""Bounded exact falsifier search; no novelty/proof inference from a zero hit."""
import itertools,random,json,pathlib
N=12;columns=[(1,0,0),(0,1,0),(0,0,1),(1,1,0),(0,1,1),(1,1,1)]
# Columns have consecutive ones, hence TU; counts use unbounded coin DP.
D={(0,0,0):1}
for col in columns:
 for a in itertools.product(range(N+1),repeat=3):
  prev=tuple(a[i]-col[i] for i in range(3))
  if min(prev)>=0:D[a]=D.get(a,0)+D.get(prev,0)
assert D[(1,1,1)]==4
# Independent explicit enumeration of the three nonsimple-root variables.
def count(a,b,c):
 return sum(1 for u in range(min(a,b)+1) for v in range(min(b,c)+1) for w in range(min(a,b,c)+1) if u+w<=a and u+v+w<=b and v+w<=c)
for a in itertools.product(range(6),repeat=3):assert D[a]==count(*a),(a,D[a],count(*a))
rng=random.Random(129);tests={};witness=None;keys=list(D)
for q in (3,4,5):
 tested=0
 for _ in range(120000):
  pts=[rng.choice(keys) for j in range(q-1)]
  last=tuple(((-sum(p[i] for p in pts))%q)+q*rng.randrange((N-((-sum(p[i] for p in pts))%q))//q+1) for i in range(3))
  pts.append(last);center=tuple(sum(p[i] for p in pts)//q for i in range(3))
  rhs=1
  for p in pts:rhs*=D[p]
  tested+=1
  if D[center]**q<rhs:
   witness={'q':q,'points':pts,'center':center,'counts':[D[p] for p in pts],'center_count':D[center]};break
 tests[q]=tested
 if witness:break
result={'domain':'A3 positive-root matrix; each RHS coordinate 0..12','independent_count_crosschecks':216,'trials':tests,'witness':witness,'scope':'finite diagnostics only; equal-weight supports of size3,4,5; not full Question1.7'}
pathlib.Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
