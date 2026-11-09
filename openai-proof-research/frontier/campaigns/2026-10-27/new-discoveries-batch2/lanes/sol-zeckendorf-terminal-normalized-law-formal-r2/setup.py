from pathlib import Path
import json,hashlib,shutil
L=Path(__file__).resolve().parent
old=L/'frozen/sol-zeckendorf-literal-game-law-formal-r1'
for n in ['Literal.lean','runner.py','Inventory.lean','Audit.lean','package.py','pins.json','owned-declarations.json']:
    shutil.copyfile(old/n,L/n)
bindings=json.loads((L/'bindings.json').read_text())
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/Mathlib/Data/Nat/Fib/Zeckendorf.lean')
sources=[P]
prior=L.parent/'sol-zeckendorf-literal-game-law-formal-r1'
for r in json.loads((old/'source-bindings.json').read_text()):
    if isinstance(r,dict):
        print(r)
for p in sources:
    data=p.read_bytes();q=L/'references'/p.name;q.parent.mkdir(exist_ok=True);q.write_bytes(data)
    assert p.read_bytes()==q.read_bytes()==data
    bindings.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=hashlib.sha256(data).hexdigest()))
(L/'bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
