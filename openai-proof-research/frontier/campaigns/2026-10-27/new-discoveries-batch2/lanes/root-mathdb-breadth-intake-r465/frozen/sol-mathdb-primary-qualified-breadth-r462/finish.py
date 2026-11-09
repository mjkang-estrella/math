import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent
refs=json.loads((L/'bindings.json').read_text());initial=[e for e in refs if e['role']!='direct-binding-original-no-expansion']
b=(json.dumps(initial,indent=2)+'\n').encode();assert hashlib.sha256(b).hexdigest()==json.loads((L/'freeze-receipt.json').read_text())['bindings_sha256'];(L/'initial-bindings.json').write_bytes(b)
exclude=['manifest.json','final-receipt.json','verification.log']
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and str(p.relative_to(L)) not in exclude:
  b=p.read_bytes();files.append(dict(path=str(p.relative_to(L)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
(L/'manifest.json').write_text(json.dumps(dict(files=files,excluded=exclude),indent=2)+'\n')
