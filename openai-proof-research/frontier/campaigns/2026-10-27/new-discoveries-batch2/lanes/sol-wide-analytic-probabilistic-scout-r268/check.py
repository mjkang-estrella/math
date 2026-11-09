"""Capped exact diagnostic; no universal conjecture is inferred."""
from work import *
from fractions import Fraction as F
from itertools import combinations
def cross(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def hull(x):
 x=sorted(set(x));lo=[];hi=[]
 for p in x:
  while len(lo)>1 and cross(lo[-2],lo[-1],p)<=0:lo.pop()
  lo.append(p)
 for p in reversed(x):
  while len(hi)>1 and cross(hi[-2],hi[-1],p)<=0:hi.pop()
  hi.append(p)
 return lo[:-1]+hi[:-1]
def admissible(x,o):
 h=hull(x+[(2*o[0]-p[0],2*o[1]-p[1]) for p in x])
 return all(any(cross(a,b,p)==0 for a,b in zip(h,h[1:]+h[:1])) for p in x)
def lines(x):
 out=set()
 for a,b,c in combinations(x,3):
  for p,q,r in [(a,b,c),(a,c,b),(b,c,a)]:
   A=p[1]-q[1];B=q[0]-p[0];C=(A*(p[0]+r[0])+B*(p[1]+r[1]))/2
   z=A or B;out.add((A/z,B/z,C/z))
 return sorted(out)
if __name__=='__main__':
 sq=[(F(a),F(b)) for a,b in [(-1,-1),(-1,1),(1,-1),(1,1)]]
 tests={str(o):admissible(sq,o) for o in [(F(0),F(0)),(F(1),F(0)),(F(0),F(1)),(F(1,2),F(1,2)),(F(100),F(0))]}
 assert list(tests.values())==[True,True,True,False,True]
 # Mechanism 2: finite arrangement of triangle center-region boundaries.
 # On a square this exactly reproduces the source cross, including boundary-only centers.
 ls=lines(sq);candidates={(F(0),F(0))}
 for (a,b,c),(d,e,f) in combinations(ls,2):
  det=a*e-b*d
  if det:candidates.add(((c*e-b*f)/det,(a*f-c*d)/det))
 good=[o for o in candidates if admissible(sq,o)]
 assert all(o[0]==0 or o[1]==0 for o in good)
 # The triple-to-set equivalence is tested independently by hulls, not reused as code.
 bad=[]
 for i in range(-6,7):
  for j in range(-6,7):
   o=(F(i,2),F(j,2));a=admissible(sq,o);b=all(admissible(list(t),o) for t in combinations(sq,3))
   if a!=b:bad.append([i,j])
 assert not bad
 interval_controls=[]
 for extra in [[(2,0)],[(-2,0),(2,0)],[(0,2)],[(2,2)],[(-2,0),(3,0)],[(2,F(1,2)),(-2,F(-1,2))]]:
  x=sq+[(F(a),F(b)) for a,b in extra]
  for axis in [0,1]:
   flags=[admissible(x,(F(i,4),F(0)) if axis==0 else (F(0),F(i,4))) for i in range(-16,17)]
   hits=[i for i,v in enumerate(flags) if v]
   assert not hits or hits==list(range(min(hits),max(hits)+1))
   interval_controls.append(dict(extra=[[str(a),str(b)] for a,b in extra],axis=axis,grid_hits=hits))
 save(L/'exact-checks.json',dict(square_tests=tests,boundary_lines=len(ls),arrangement_vertices=len(candidates),admissible_vertices=[[str(v) for v in o] for o in good],triple_equivalence_grid_points=169,interval_controls=interval_controls,failures=bad,scope='diagnostic only; exact fractions; universal restricted witness theorem proved in prose, not inferred from grid'))
 print('exact checks PASS; finite diagnostic only')
