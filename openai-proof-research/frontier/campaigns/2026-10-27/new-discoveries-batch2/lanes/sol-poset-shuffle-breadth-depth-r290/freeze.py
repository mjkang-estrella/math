import pathlib,hashlib,json,shutil
L=pathlib.Path(__file__).resolve().parent; B=L.parent.parent; R=B.parents[3]
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
for p in [R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json']:
 d=L/'administrative'/p.name;d.parent.mkdir(exist_ok=True);shutil.copyfile(p,d)
 records.append(dict(kind='administrative snapshot',original=str(p),copy=str(d),sha256=digest(d)))
old=L.parent/'sol-older-primary-wide-scout-r289'
paths=[old/x for x in ['SUMMARY.md','discovery.md','SCOUTING.md','progress.md','provenance.json','primarybindings.json','checks.json','failures.md']]
paths += list((old/'primary').glob('*1412*'))
paths += [L.parent/'root-scout-r289-disposition'/'STATUS.md']
for p in paths:
 if not p.is_file(): records.append(dict(missing=str(p)));continue
 h=digest(p); d=L/'frozen'/p.parent.name/p.name;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,d)
 assert digest(d)==h==digest(p)
 records.append(dict(kind='scientific frozen before reading',original=str(p),copy=str(d),sha256=h))
(L/'freeze-bindings.json').write_text(json.dumps(records,indent=2))
print(json.dumps(records,indent=2))
