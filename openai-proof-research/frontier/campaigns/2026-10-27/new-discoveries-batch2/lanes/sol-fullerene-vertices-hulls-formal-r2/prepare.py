from pathlib import Path
import json,hashlib,shutil
L=Path(__file__).resolve().parent
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/Mathlib')
rows=[]
for s in ['Analysis/Convex/KreinMilman.lean','Analysis/Convex/Extreme.lean','LinearAlgebra/FiniteDimensional/Basic.lean','LinearAlgebra/FiniteDimensional/Lemmas.lean','LinearAlgebra/Dimension/Finrank.lean']:
 p=P/s;d=L/'mathlib'/s;d.parent.mkdir(parents=True,exist_ok=True);a=p.read_bytes();d.write_bytes(a);assert p.read_bytes()==a
 rows.append(dict(original=str(p),copy=str(d.relative_to(L)),sha256=hashlib.sha256(a).hexdigest()))
(L/'mathlib-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
shutil.copyfile(L/'frozen/sol-fullerene-rational-polytope-formal-r1/runner.py',L/'runner.py')
