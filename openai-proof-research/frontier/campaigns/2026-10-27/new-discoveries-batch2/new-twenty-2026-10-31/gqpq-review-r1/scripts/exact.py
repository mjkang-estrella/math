from itertools import product
from fractions import Fraction
from pathlib import Path
import json
D=Path(__file__).resolve().parents[1]
cells=[[[2],[0,1],[0,1,2]],[[0,1],[1,2],[0,2]],[[0,1],[2],[1,2]]]
H=[(i,j,z) for i,j in product(range(3),repeat=2) for z in cells[i][j]]
A=[[0,0,1],[-1,0,1],[-1,0,0]];B=[[1,0,0],[0,0,-1],[0,0,0]];C=[[-1,0,0],[0,0,1],[0,-1,0]]
w=[2 if p==(0,0,2) else 0 if p==(0,2,2) else 1 for p in H]
lines=[]
for axis,u,v in product(range(3),repeat=3):
 lines.append([t for t,p in enumerate(H) if tuple(p[a] for a in range(3) if a!=axis)==(u,v)])
sums=[sum(w[t] for t in l) for l in lines]
assert len(H)==17 and sum(w)==17 and max(sums)==2
assert all(A[j][z]+B[i][z]+C[i][j]==0 for i,j,z in H)
T=[[A[i][j]+B[i][j]+C[i][j] for j in range(3)] for i in range(3)]
coeff={(i,j):(T[i][j] if i==j else T[i][j]+T[j][i]) for i in range(3) for j in range(i,3)}
assert coeff=={(0,0):0,(0,1):-1,(0,2):0,(1,1):0,(1,2):0,(2,2):0}
# Independent exact minimum cover, with branching only on lines covering the first uncovered point.
masks=[sum(1<<i for i in l) for l in lines];full=(1<<17)-1
from functools import lru_cache
@lru_cache(None)
def cover(mask):
 if mask==full:return 0
 p=next(i for i in range(17) if not(mask>>i&1))
 return 1+min(cover(mask|m) for m in masks if m>>p&1)
assert cover(0)==9
# Sanity: cyclic group order 3 has all line sums 1; source's arbitrary partition is essential.
cyclic=[(i,j,(i+j)%3) for i,j in product(range(3),repeat=2)]
assert not set(cyclic)<=set(H)
# Negative perturbations expose each certificate's specific failure, not foundational consistency.
bad=w.copy();bad[0]+=1
assert max(sum(bad[t] for t in l) for l in lines)>2
assert A[0][1]+B[0][1]+C[0][0]!=0 # (0,0,1) is excluded
r=dict(H=H,integer_weights=w,line_sums=sums,fractional_total=str(Fraction(sum(w),2)),minimum_cover=cover(0),DP_states=cover.cache_info().currsize,T=T,polynomial_coefficients={str(k):v for k,v in coeff.items()},obstruction='-r0*r1 < 0 for all positive class sizes',negative_controls=2)
(D/'exact.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))
