from pathlib import Path
from itertools import product,combinations
import json
O=Path(__file__).resolve().parent
F=[list(x) for x in product(range(2),repeat=6) if sum(x)<=2]
a={'mathdb_id':382487,'parameters':{'r':6,'t':2,'n':2},'family':F,'size':len(F),'minimum_pair_agreement':min(sum(a==b for a,b in zip(x,y)) for x,y in combinations(F,2)),'fixed_coordinates':[j for j in range(6) if len({x[j] for x in F})==1],'conjectured_terms':[2**4-1+2,4*2**3-3*2**2],'status':'EXECUTED; publicly subsumed by Hou-Hu A_2(2,2;6), not a new outcome'}
assert a['size']==22 and a['minimum_pair_agreement']==2 and a['fixed_coordinates']==[] and max(a['conjectured_terms'])==20
(O/'bounded-calculation.json').write_text(json.dumps(a,indent=2)+'\n');print({k:v for k,v in a.items() if k!='family'})
