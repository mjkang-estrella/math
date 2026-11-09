from research import *
from fractions import Fraction as F
def center(S):return sorted(d for d in {abs(x-min(S)) for x in S} if all(x-d in S or x+d in S for x in S))
rows=[]
# Exact exhaustive finite grid diagnostics, never an arbitrary-compact conclusion.
for N in range(1,14):
 attainable=set()
 for bits in range(1<<(N-1)):
  S={0,N}|{i+1 for i in range(N-1) if bits>>i&1}
  attainable.add(tuple(center(S)))
 rows.append({'diameter':N,'distinct_centers':len(attainable)})
M=F(3);C={F(0),F(1),F(3,2),M};K=set(F(i,2) for i in range(37) if abs(F(i,2)-9)>=3 or abs(F(i,2)-9) in C)
assert F(21,2) in K and F(19,2) not in K and F(23,2) not in K
# Finite approximants with exactly trivial center converging to [0,1].
closure=[]
for n in [3,5,9,17]:
 S={F(i,n) for i in range(n+1)}|{F(1,2*n+1)}
 assert center(S)==[0]
 closure.append({'n':n,'center':[str(t) for t in center(S)],'Hausdorff_upper_bound':str(F(1,n))})
save('checks-result.json',{'finite_grid':rows,'Hausdorff_extra_distances':closure,'aligned_holes_failure':{'C':[str(x) for x in sorted(C)],'M':'3','witness':'10.5','wanted_distance':'1','both_partners_absent':True},'scope':'exact finite rational checks, not full compact realization'})
print('PASS: finite diagnostics; explicit aligned-hole failure; Hausdorff gain example')
