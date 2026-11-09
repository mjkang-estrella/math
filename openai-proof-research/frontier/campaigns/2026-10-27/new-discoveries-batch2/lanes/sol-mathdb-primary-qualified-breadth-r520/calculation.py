from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import json
P=Path(__file__).resolve().parent
out={'target':365021,'scope':'All positive distinct integer speed sets of cardinality 1..5 contained in 1..12; exact rational interval intersection, not full conjecture','cases':0,'empty_feasible':[],'grid_misses':[],'singleton_only_cases':0}
for n in range(1,6):
 for V in combinations(range(1,13),n):
  intervals=[(Q(0),Q(1))]
  for v in V:
   good=[(Q((n+1)*a+1,(n+1)*v),Q((n+1)*(a+1)-1,(n+1)*v)) for a in range(v)]
   intervals=[(max(a,c),min(b,d)) for a,b in intervals for c,d in good if max(a,c)<=min(b,d)]
  # ceil(log2(vmax)+1) = (vmax-1).bit_length()+1, exactly, including powers of 2.
  D=2**((V[-1]-1).bit_length()+1)*(n+1)*V[-1]
  hit=any(-(-a.numerator*D//a.denominator)<=b.numerator*D//b.denominator for a,b in intervals)
  out['cases']+=1
  if not intervals:out['empty_feasible'].append(V)
  if not hit:out['grid_misses'].append(V)
  if intervals and all(a==b for a,b in intervals):out['singleton_only_cases']+=1
out['conclusion']='Finite diagnostic only. No universal bound, proof, novelty, or registry clearance.'
(P/'calculation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
