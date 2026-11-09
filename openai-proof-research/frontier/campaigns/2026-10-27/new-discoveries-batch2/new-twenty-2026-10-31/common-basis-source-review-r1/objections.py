from pathlib import Path
import json,itertools
L=Path(__file__).resolve().parent;d=json.loads((L/'independent-math.json').read_text());out={}
for x,bs in d['deletion_extendible'].items():
 F=set(map(frozenset,bs));bad=next(((sorted(a),sorted(b),e) for a in F for b in F for e in a-b if all((a-{e})|{f} not in F for f in b-a)),None);out[x]={'basis_exchange_failure':bad}
(L/'nonmatroid-extendible-families.json').write_text(json.dumps(out,indent=2));print(out)
