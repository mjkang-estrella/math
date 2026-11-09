from itertools import permutations
from pathlib import Path
import json
r=Path(__file__).resolve().parents[1];nodes=0;sol=0;best=99;w=None
# Hub is cycle position 0; leaves unordered; cycle reversal removed.
for cyc in permutations(range(1,12),7):
 if cyc[1]>cyc[-1]:continue
 nodes+=1
 sums=[cyc[i]+cyc[(i+1)%7] for i in range(7)]
 if len(set(sums))<7 or max(sums)-min(sums)>10:continue
 leaves=sorted(set(range(1,12))-set(cyc));sums += [cyc[0]+x for x in leaves]
 if len(set(sums))==11 and max(sums)-min(sums)==10:
  sol+=1
  if min(sums)<best:best=min(sums);w=list(cyc)+leaves
out=dict(cycle_reversal_reduced_assignments=nodes,valid=sol,minimum_endpoint_sum=best,strength=22+best,witness=w,exhaustive=True)
(r/'logs/exact.json').write_text(json.dumps(out,indent=2));print(out)
