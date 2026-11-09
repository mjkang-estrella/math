import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent
v={'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':[]}
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in v['excluded_exact_paths']:
  b=p.read_bytes();v['files'].append({'path':str(p.relative_to(L)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(L/'manifest.json').write_text(json.dumps(v,indent=2)+'\n')
