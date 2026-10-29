from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
rows=json.loads((L/'finalmanifest.json').read_text())
for r in rows:
 p=L/r['path'];h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(131072),b''):h.update(b)
 assert p.stat().st_size==r['bytes'] and h.hexdigest()==r['sha256'],r['path']
print(json.dumps({'verified_manifest_files':len(rows),'status':'PASS'}))
