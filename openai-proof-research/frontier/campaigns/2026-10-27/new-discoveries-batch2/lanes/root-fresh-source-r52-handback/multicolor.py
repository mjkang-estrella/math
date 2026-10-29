import itertools,json
from collections import Counter
from fractions import Fraction as Q
# Each K3,3 edge is allocated to one of three colors; retain first2 color margins.
D=Counter()
for cs in itertools.product(range(3),repeat=9):
 a=[0]*12
 for e,c in enumerate(cs):
  if c<2:a[6*c+e//3]+=1;a[6*c+3+e%3]+=1
 D[tuple(a)]+=1
central=(1,)*12
# Explicit fractional vertex of 3x3x3 line-sum polytope (twice entries).
X=[[[2,0,0],[0,1,1],[0,1,1]],[[0,1,1],[1,1,0],[1,0,1]],[[0,1,1],[1,0,1],[1,1,0]]]
S=[(i,j,k) for i,j,k in itertools.product(range(3),repeat=3) if X[k][i][j]]
rows=[]
for axis in range(3):
 for a,b in itertools.product(range(3),repeat=2):
  row=[]
  for x in S:
   rest=[x[t] for t in range(3) if t!=axis];row.append(Q(rest==[a,b]))
  rows.append(row)
A=[r[:] for r in rows];rank=0;pivots=[]
for col in range(len(S)):
 p=next((i for i in range(rank,len(A)) if A[i][col]),None)
 if p is None:continue
 A[rank],A[p]=A[p],A[rank];scale=A[rank][col];A[rank]=[x/scale for x in A[rank]]
 for i in range(len(A)):
  if i!=rank:
   scale=A[i][col];A[i]=[x-scale*y for x,y in zip(A[i],A[rank])]
 pivots.append(col);rank+=1
assert rank==len(S)
for row in rows:assert sum(a*X[k][i][j] for a,(i,j,k) in zip(row,S))==2
mx=max(D.values());arg=next(k for k,v in D.items() if v==mx)
print(json.dumps({'central_coefficient':D[central],'max_coefficient':mx,'max_first_two_margins':arg,'fractional_vertex_twice_slices':X,'support':len(S),'constraint_rank_on_support':rank,'conclusion':'Fractional vertex obstructs multicolor total-unimodularity proof, NOT source Jensen counterexample.'},indent=2))
