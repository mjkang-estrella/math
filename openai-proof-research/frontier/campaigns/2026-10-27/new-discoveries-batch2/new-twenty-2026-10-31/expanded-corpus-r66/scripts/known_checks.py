from pathlib import Path
from fractions import Fraction
import json
D=Path(__file__).resolve().parents[1]
p=[0,2,7,21,17,12,4,9,14,19,1,8,15,22,6,3,20,13,11,18,5,10,16]
assert sorted(p)==list(range(23))
types=[]
for s in range(23):
 q=[(a+s)%23 for a in p];seen=set();sizes=[]
 for a in range(23):
  if a in seen:continue
  v=a;l=0
  while v not in seen:seen.add(v);l+=1;v=q[v]
  sizes.append(l)
 types.append(sorted(sizes))
assert types==[[1,22]]*23
assert not any(all(p[t]==(a*t+b)%23 for t in range(23)) for a in range(1,23) for b in range(23))
r=Fraction(2*(4+3)**2,2*2*2*(2-1)**2);assert r==Fraction(49,4) and r>2
out={'known_371073':{'permutation':p,'shift_cycle_types':types,'nonaffine':True,'scope':'Independent check of the primary paper witness; no discovery'},'370838_parameter_defect':{'n':4,'m':3,'Delta':2,'k':1,'middle_expression':str(r),'scope':'Elementary violation only; excluded substantive credit'}}
(D/'outputs/known-checks.json').write_text(json.dumps(out,indent=2)+'\n');print('Known n23 witness and elementary P4 parameter calculation verified.')
