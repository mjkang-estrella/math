from pathlib import Path
import sys,json,hashlib
L=Path(__file__).resolve().parent
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/Mathlib')
rows=json.loads((L/'mathlib-bindings.json').read_text())
for s in sys.argv[1:]:
 p=P/s;d=L/'mathlib'/s;d.parent.mkdir(parents=True,exist_ok=True);a=p.read_bytes();d.write_bytes(a);assert p.read_bytes()==a
 rows.append(dict(original=str(p),copy=str(d.relative_to(L)),sha256=hashlib.sha256(a).hexdigest()))
(L/'mathlib-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
