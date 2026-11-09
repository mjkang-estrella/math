import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent
excluded={'manifest.json','verification-receipt.json'}
entries=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and str(p.relative_to(P)) not in excluded:
  b=p.read_bytes();entries.append({'path':str(p.relative_to(P)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'manifest.json').write_text(json.dumps({'excluded_exact_paths':sorted(excluded),'files':entries},indent=2)+'\n')
b=(P/'manifest.json').read_bytes();print(json.dumps({'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'payloads':len(entries)}))
