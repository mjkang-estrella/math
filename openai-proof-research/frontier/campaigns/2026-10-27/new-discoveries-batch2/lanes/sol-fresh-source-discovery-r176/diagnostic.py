import checks,json,itertools as it,random
from pathlib import Path
rng=random.Random(176);out=[]
for k in range(3,7):
 for cfg in it.combinations(it.product(range(3),repeat=2),k):
  P=set(cfg);o=checks.groebner_objection(P)
  if o:
   out.append(dict(cells=sorted(P),objection=o,diagnostic=checks.diagnostic(P,4)));break
 if out:break
Path(__file__).with_name('diagnostics.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
