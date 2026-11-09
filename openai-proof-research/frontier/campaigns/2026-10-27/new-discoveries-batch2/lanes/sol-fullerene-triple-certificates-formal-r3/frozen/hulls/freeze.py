import pathlib,hashlib,json,shutil
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
items=[]
for lane,names in [('root-fullerene-geometry-disposition-r4',['STATUS.md']),('sol-fullerene-rational-polytope-formal-r1',['Literal.lean','InstanceG.lean','InstanceH.lean','SUMMARY.md','RUN.md','runner.py','Audit.lean','Inventory.lean','audit_receipt.py','replay.py','pins.json','verification-receipt.json','replay-receipt.json','coordinate-check.json','audit.json'])]:
 for name in names:
  p=L.parent/lane/name
  d=L/'frozen'/lane/name;d.parent.mkdir(parents=True,exist_ok=True)
  a=p.read_bytes();d.write_bytes(a);assert p.read_bytes()==d.read_bytes()==a
  items.append(dict(original=str(p),copy=str(d.relative_to(L)),sha256=hashlib.sha256(a).hexdigest()))
for p in (L.parent/'sol-fullerene-rational-polytope-formal-r1'/'harness').iterdir():
 if p.is_file():
  d=L/'frozen'/'harness'/p.name;d.parent.mkdir(parents=True,exist_ok=True);a=p.read_bytes();d.write_bytes(a);assert p.read_bytes()==a
  items.append(dict(original=str(p),copy=str(d.relative_to(L)),sha256=hashlib.sha256(a).hexdigest()))
for name in ['ledger.json','prior-campaign-context.json','AGENTS.md']:
 d=L/'administrative'/name;d.parent.mkdir(exist_ok=True);shutil.copyfile(B/name,d)
for name in ['Literal.lean','InstanceG.lean','InstanceH.lean']:
 shutil.copyfile(L/'frozen'/'sol-fullerene-rational-polytope-formal-r1'/name,L/name)
(L/'source-bindings.json').write_text(json.dumps(items,indent=2)+'\n')
print('frozen',len(items))
