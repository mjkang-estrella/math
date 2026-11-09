from fractions import Fraction
from itertools import permutations
import json
from pathlib import Path
D=Path(__file__).resolve().parents[1];out=[]
for n in range(4,9):
 eps=Fraction(1,n);m=0;t=0
 for p in permutations(range(n)):
  m+=1;seen={0};v=p[0]
  while v not in seen:seen.add(v);v=p[v]
  tour=len(seen)==n
  t+=tour
 # distinct permutations agree at most n-2 entries, hence exposing functional <P,.>
 # for nontour P and tour Q, gap >= n+eps-(n-2)*(1+eps)
 gap=n+eps-(n-2)*(1+eps);assert gap>0
 o=dict(n=n,permutations=m,tours=t,epsilon=str(eps),min_cross_exposure_gap=str(gap));out.append(o);print(o)
(D/'outputs/polytope.json').write_text(json.dumps(out,indent=2)+'\n')
