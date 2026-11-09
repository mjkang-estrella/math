from pathlib import Path
import json,itertools
from fractions import Fraction as F
L=Path(__file__).resolve().parent
d=json.loads((L/'witness-best.json').read_text());edges=list(itertools.combinations(range(4),2))
values={tuple(s):tuple(map(F,v)) for s,v in zip(d['states'],d['grid_values'])}
assert set(values)==set(itertools.product(range(3),repeat=6))
checks=0
for s,v in values.items():
 assert sum(v)==1 and min(v)>=0
 for k,(i,j) in enumerate(edges):
  if s[k]<2:
   t=list(s);t[k]+=1;w=values[tuple(t)]
   assert w[i]>=v[i] and w[j]<=v[j];checks+=2
 for perm in itertools.permutations(range(4)):
  mat=[[1]*4 for _ in range(4)]
  for (i,j),a in zip(edges,s):mat[perm[i]][perm[j]]=a;mat[perm[j]][perm[i]]=2-a
  t=tuple(mat[i][j] for i,j in edges);w=values[t]
  assert all(w[perm[i]]==v[i] for i in range(4));checks+=4
s=tuple(d['state']);P=[[1]*4 for _ in range(4)]
for (i,j),a in zip(edges,s):P[i][j]=a;P[j][i]=2-a
assert all(P[i][j]>=P[i+1][j] for i in range(3) for j in range(4))
assert values[s]==(F(1,4),F(0),F(3,8),F(3,8))
# Source graph-polytope bound: arcs from vertices 1 and 2 all land in {1,2}.
assert values[s][0]+values[s][1]<F(1,2)
(L/'witness-verification.json').write_text(json.dumps({'PASS':True,'checks':checks,'arithmetic':'stdlib Fraction; no LP or quotient reuse','win_vector':d['win_vector'],'P_twice':P,'scope':'grid certificate; multilinear interpolation proof needed for universal map; source approximation bridge needed for tournaments'},indent=2))
print('PASS',checks)
