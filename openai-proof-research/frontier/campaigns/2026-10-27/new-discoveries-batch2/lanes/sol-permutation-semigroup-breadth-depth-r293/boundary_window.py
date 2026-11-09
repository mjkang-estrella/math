from pathlib import Path
from math import gcd
import json
from checks import dp,certify
L=Path(__file__).resolve().parent;tested=0;passing=[];nonfirst=0
for a in range(12,181):
 candidates=[(a,b,2*a) for b in range(a+1,2*a)]+[(a,2*a,d) for d in range(2*a+1,3*a+1)]
 for t in candidates:
  if gcd(gcd(*t[:2]),t[2])!=1 or len({v%3 for v in t})<3:continue
  tested+=1
  if dp(t,12*a,True) is not None:passing.append(certify(t))
(L/'window-result.json').write_text(json.dumps(dict(range=[12,180],eligible_tested=tested,passing=passing),indent=2));print(tested,passing)
