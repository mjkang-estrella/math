import pathlib,hashlib,json
L=pathlib.Path(__file__).resolve().parent
B=L.parent
entries=[]
def freeze(p,kind):
    p=p.resolve(); data=p.read_bytes(); h=hashlib.sha256(data).hexdigest()
    dest=L/kind/(p.parent.name+'--'+p.name)
    dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(data)
    assert p.read_bytes()==dest.read_bytes()==data
    entries.append(dict(original=str(p),copy=str(dest.relative_to(L)),sha256=h,kind=kind))
for name in ['AUDIT.md','rational-realizations.json','realize.py','verify.py','provenance.json']:
    freeze(B/'sol-fullerene-literal-feasibility-prior-r2'/name,'frozen')
freeze(B/'root-fullerene-feasibility-disposition-r3'/'STATUS.md','frozen')
for name in ['runner.py','Audit.lean','Inventory.lean','pins.json','replay.py','package.py','RUN.md']:
    freeze(B/'sol-zeckendorf-literal-game-law-formal-r1'/name,'harness')
for name in ['ledger.json','prior-campaign-context.json','AGENTS.md']:
    freeze(B.parent/name,'administrative')
freeze(B.parents[4]/'AGENTS.md','administrative')
(L/'source-bindings.json').write_text(json.dumps(entries,indent=2)+'\n')
print(json.dumps(entries,indent=2))
