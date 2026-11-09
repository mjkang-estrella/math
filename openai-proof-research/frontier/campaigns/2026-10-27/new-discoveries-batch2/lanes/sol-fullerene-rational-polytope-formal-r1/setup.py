exec(open(__file__.replace('setup.py','freeze.py')).read().split("for name in ['AUDIT.md'")[0])
for name in ['fullerenes.pdf','fullerenes.txt']:
    freeze(B/'sol-fullerene-literal-feasibility-prior-r2'/'prior'/name,'primary')
old=json.loads((L/'source-bindings.json').read_text())
(L/'source-bindings.json').write_text(json.dumps(old+entries,indent=2)+'\n')
P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
rows=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted((P/'mathlib'/'Mathlib').rglob('*.lean'))]
(L/'mathlib-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
for name in ['runner.py','Audit.lean','Inventory.lean','pins.json']:
    (L/name).write_bytes((L/'harness'/('sol-zeckendorf-literal-game-law-formal-r1--'+name)).read_bytes())
print('frozen primary and',len(rows),'mathlib files; harness copied')
