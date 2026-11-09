import pathlib, hashlib, json, shutil
root=pathlib.Path(__file__).resolve().parent
batch=root.parent.parent
prior=root.parent/'sol-zeckendorf-literal-game-law-formal-r1'
files=[p for p in prior.iterdir() if p.is_file() and p.suffix in ('.lean','.md','.json','.py')]
files += [root.parent/'root-zeckendorf-component-disposition-r2'/'STATUS.md']
records=[]
for p in files:
    data=p.read_bytes(); digest=hashlib.sha256(data).hexdigest()
    q=root/'frozen'/p.parent.name/p.name
    q.parent.mkdir(parents=True,exist_ok=True); q.write_bytes(data)
    assert p.read_bytes()==data==q.read_bytes()
    records.append(dict(original=str(p),copy=str(q.relative_to(root)),sha256=digest))
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
    q=root/'administrative'/name;q.parent.mkdir(exist_ok=True);q.write_bytes((batch/name).read_bytes())
(root/'bindings.json').write_text(json.dumps(records,indent=2)+'\n')
print('frozen',len(records))
