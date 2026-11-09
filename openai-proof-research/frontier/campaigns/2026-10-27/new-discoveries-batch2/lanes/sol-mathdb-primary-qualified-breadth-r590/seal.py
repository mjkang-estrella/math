import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent
exclude=['manifest.json','final-verification-receipt.json']
files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and str(p.relative_to(P)) not in exclude:
  b=p.read_bytes();files.append(dict(path=str(p.relative_to(P)),sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
(P/'manifest.json').write_text(json.dumps(dict(excluded_exact_paths=exclude,files=files),indent=2)+'\n')
b=(P/'manifest.json').read_bytes();print(json.dumps(dict(manifest_sha256=hashlib.sha256(b).hexdigest(),manifest_size=len(b),payload_files=len(files))))
