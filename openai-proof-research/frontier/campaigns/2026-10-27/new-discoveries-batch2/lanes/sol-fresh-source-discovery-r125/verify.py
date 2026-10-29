import json,hashlib,datetime
from pathlib import Path
p=Path(__file__).resolve().parent
m=p/'finalmanifest.json';j=json.loads(m.read_text());bad=[]
for x in j['files']:
 q=p/x['path'];h=hashlib.sha256()
 try:
  with q.open('rb') as f:
   while b:=f.read(65536):h.update(b)
  if h.hexdigest()!=x['sha256'] or q.stat().st_size!=x['bytes']:bad.append(x['path'])
 except OSError:bad.append(x['path'])
actual={str(q.relative_to(p)) for q in p.rglob('*') if q.is_file() and q.name not in ['finalmanifest.json','manifest-verification.json'] and '__pycache__' not in q.parts}
assert actual=={x['path'] for x in j['files']},'membership'
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(m.read_bytes()).hexdigest(),'files':len(j['files']),'mismatches':bad,'pass':not bad,'scope':'artifact integrity, not mathematical proof or novelty'}
(p/'manifest-verification.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));assert not bad
