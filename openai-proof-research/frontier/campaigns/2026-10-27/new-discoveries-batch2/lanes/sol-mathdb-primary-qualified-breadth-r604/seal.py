import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parent;excluded={'manifest.json','final-verification-receipt.json'}
rows=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and str(p.relative_to(D)) not in excluded:
  b=p.read_bytes();rows.append({'path':str(p.relative_to(D)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(D/'manifest.json').write_text(json.dumps({'excluded_exact_paths':sorted(excluded),'files':rows},indent=2)+'\n')
