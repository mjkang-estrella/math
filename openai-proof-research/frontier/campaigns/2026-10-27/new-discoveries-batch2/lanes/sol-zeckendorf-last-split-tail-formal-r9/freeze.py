from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent
B=L.parent.parent
rows=[]
def freeze(p,rel):
 a=p.read_bytes(); h=hashlib.sha256(a).hexdigest(); d=L/rel;d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(a)
 assert p.read_bytes()==a==d.read_bytes()
 rows.append(dict(original=str(p),copy=str(d.relative_to(L)),sha256=h))
for f in ['ledger.json','prior-campaign-context.json','AGENTS.md']:
 freeze(B/f,'administrative/'+f)
for lane,files in [
 ('sol-zeckendorf-concentration-assembly-formal-r8',None),
 ('root-zeckendorf-interval-disposition-r9',['STATUS.md']),
 ('sol-zeckendorf-mixing-obstruction-r284',['PROOF.md','SUMMARY.md','source-bindings.json']),
 ('sol-zeckendorf-mixing-preliminary-review-r1',None),
 ('sol-zeckendorf-mixing-source-prior-review-r2',None)]:
 p=L.parent/lane
 fs=[x for x in p.iterdir() if x.is_file() and (x.suffix in ['.lean','.py','.sh','.md'] or x.name in ['audit.json','bindings.json','pins.json','replay-receipt.json','verification-receipt.json','provenance.json','freeze.json','immutable-references.json']) and not x.name.startswith('attempt-')] if files is None else [p/f for f in files]
 for f in sorted(fs):freeze(f,'frozen/'+lane+'/'+f.name)
(L/'freeze.json').write_text(json.dumps(rows,indent=2)+'\n')
print('frozen',len(rows),'files; scientific sources not yet read')
