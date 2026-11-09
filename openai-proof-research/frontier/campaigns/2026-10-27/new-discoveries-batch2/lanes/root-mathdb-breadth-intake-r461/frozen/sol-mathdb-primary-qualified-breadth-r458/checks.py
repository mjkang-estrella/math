from itertools import combinations,permutations
from math import isqrt
import json
from pathlib import Path
P=[(0,0),(8,0),(4,3),(4,-3)]
dist=[(a[0]-b[0])**2+(a[1]-b[1])**2 for a,b in combinations(P,2)]
assert all(isqrt(d)**2==d for d in dist)
areas=[(b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0]) for a,b,c in combinations(P,3)]
assert all(areas)
M=[[x*x+y*y,x,y,1] for x,y in P]
det=0
for p in permutations(range(4)):
 s=(-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4));v=s
 for i in range(4):v*=M[i][p[i]]
 det+=v
assert det!=0
# Enumerate every biclique's edge set in C5 and exact partitions.
E={tuple(sorted((i,(i+1)%5))) for i in range(5)}; bic=set()
for mask in range(1,1<<5):
 A={i for i in range(5) if mask>>i&1}
 for mask2 in range(1,1<<5):
  B={i for i in range(5) if mask2>>i&1}
  if A&B:continue
  edges=frozenset(tuple(sorted((a,b))) for a in A for b in B)
  if edges<=E:bic.add(edges)
assert max(map(len,bic))==2
assert not any(a.isdisjoint(b) and a|b==E for a in bic for b in bic)
assert any(a.isdisjoint(b) and (a|b).isdisjoint(c) and a|b|c==E for a in bic for b in bic for c in bic)
assert not any(all(cs[a]!=cs[b] for a,b in E) for cs in __import__('itertools').product(range(2),repeat=5))
assert all([0,1,0,1,2][a]!=[0,1,0,1,2][b] for a,b in E)
out={'317262':{'points':P,'distance_squares':dist,'oriented_double_areas':areas,'concyclic_determinant':det,'status':'exact literal counterexample; routine scope issue, zero credit'},'318334':{'graph':'C5','chromatic_number':3,'biclique_partition_number':3,'largest_biclique_edges':2,'enumerated_biclique_edge_sets':len(bic),'status':'exact literal counterexample; routine wording issue, zero credit'}}
(Path(__file__).parent/'bounded-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
