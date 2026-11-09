from fractions import Fraction as F
from pathlib import Path
import json
D=Path(__file__).resolve().parents[1];svals=[F(k,16) for k in range(16,257)];rows=[];count=0
for a in range(1,9):
 for b in [F(k,8) for k in range(1,17)]:
  cy=max((a*a+b*b)/(s*s*((s-a)**2+b*b)) for s in svals)
  for t in [F(1,4),F(1,2),F(3,4)]:
   cz=max(t*t*(a*a+b*b)/(s*s*((s-t*a)**2+(t*b)**2)) for s in svals);count+=1
   if cz>cy:rows.append({'y':[str(a),str(b)],'t':str(t),'sampled_cy_sq':str(cy),'sampled_cz_sq':str(cz)})
(D/'outputs/cassinian-search.json').write_text(json.dumps({'tested':count,'boundary_sample':'s=1..16 step1/16','positive_diagnostics':rows,'certificate':'formal/Cassinian.lean proves continuum boundary bound for y=4+i,t=1/2,r=7/4','limitation':'finite sampling of a continuous boundary is not a supremum proof'},indent=2));print(count,len(rows))
