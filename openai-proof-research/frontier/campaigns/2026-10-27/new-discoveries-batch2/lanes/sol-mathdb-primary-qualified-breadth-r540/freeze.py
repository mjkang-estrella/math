import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent
files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and p.name not in {'manifest.json','verification-receipt.json'}:
  b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(P/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':files},indent=2,sort_keys=True)+'\n')
