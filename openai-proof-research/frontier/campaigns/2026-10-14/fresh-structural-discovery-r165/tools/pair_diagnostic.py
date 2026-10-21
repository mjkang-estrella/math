from fractions import Fraction as F
import json
from pathlib import Path
r=Path(__file__).resolve().parents[1]
cases=0;dominated=0;pairs=0
for weights in [(1,1,2,2,3,3),(3,3,2,2,1,1),(1,1,1,1,1,1)]:
 q=[F(w,sum(weights)) for w in weights]
 for extra in [set(),{(0,1),(1,0)},{(0,1),(1,0),(2,3),(3,2)}]:
  bad=lambda x,z:x==z or (x,z) in extra
  delta=max(sum((q[z] for z in range(6) if bad(x,z)),F(0)) for x in range(6))
  Z=sum((q[x]*q[z] for x in range(6) for z in range(6) if not bad(x,z)),F(0))
  for mask in range(1,64):
   A=[i for i in range(6) if mask>>i&1];a=sum((q[i] for i in A),F(0));qa=[q[i]/a if i in A else F(0) for i in range(6)]
   badmass=sum((qa[x]*qa[z] for x in range(6) for z in range(6) if bad(x,z)),F(0))
   assert badmass<=delta/a
   cases+=1
   if a>=2*delta:
    ZA=1-badmass;assert ZA>=F(1,2);dominated+=1
    for x in range(6):
     for z in range(6):
      old=q[x]*q[z]/Z if not bad(x,z) else F(0)
      new=qa[x]*qa[z]/ZA if not bad(x,z) else F(0)
      assert new<=2/a**2*old;pairs+=1
out={'scope':'Exact finite rational diagnostic only; no universal mathematical grade','distributions':3,'conflict_relations_per_distribution':3,'restriction_cases':cases,'normalizer_and_domination_cases':dominated,'pointwise_pair_comparisons':pairs,'result':'all tested inequalities hold'}
(r/'notes/pair-diagnostic.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
