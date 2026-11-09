from pathlib import Path
from itertools import permutations
from fractions import Fraction
import json
O=Path(__file__).resolve().parent
ans=[]; prev=[0,1]
for n in range(1,9):
 c=[0]*(n+1)
 if n==1:c[1]=1
 else:
  for k in range(1,n+1):c[k]=(prev[k-1] if k-1<len(prev) else 0)+k*sum(prev[k:])
 counts=[0]*(n+1)
 for p in permutations(range(n)):
  bad=any(p[k]<p[i]<p[i+1]<p[l] for i in range(n-3) for k in range(i+2,n-1) for l in range(k+1,n))
  if not bad:
   low=n;r=0
   for z in reversed(p):
    if z<low:r+=1;low=z
   counts[r]+=1
 ans.append(dict(n=n,recurrence=c,enumeration=counts,match=c==counts));prev=c
out=dict(refinement_id=345965,interpretation='adjacent first two entries of vincular 2314, exact permutation enumeration; finite evidence only, no universal proof or novelty clearance',results=ans,published_clique_bridge=dict(id=346379,coefficient=str(Fraction(23,82)),conjectured=str(Fraction(7,25)),strict_gap=str(Fraction(23,82)-Fraction(7,25)),meaning='Published Theorem 1.4 gives self-complementary graphs with cp>=23/164*n^2+o(n^2), so cp(G)+cp(complement G)>=23/82*n^2+o(n^2) along an infinite sequence. Positive gap contradicts claimed asymptotic. Source result, zero credit.'))
assert all(v['match'] for v in ans)
assert Fraction(23,82)>Fraction(7,25)
(O/'bounded-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
