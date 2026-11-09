import pathlib,hashlib,json
P=pathlib.Path(__file__).resolve().parent
excluded=['manifest.json','final-verification-receipt.json']
files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and str(p.relative_to(P)) not in excluded:
  b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(P/'manifest.json').write_text(json.dumps({'excluded_exact_paths':excluded,'files':files},indent=2)+'\n')
