import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
j=json.loads((L/'finalmanifest.json').read_bytes())
errors=[]
for r in j['files']:
 p=L/r['path']
 if not p.exists() or len(p.read_bytes())!=r['bytes'] or hashlib.sha256(p.read_bytes()).hexdigest()!=r['sha256']:errors.append(r['path'])
lines=(L/'finalmanifest.sha256').read_text().splitlines()
assert lines==[f"{r['sha256']}  {r['path']}" for r in j['files']]
assert not errors
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',entries=len(j['files']),errors=errors,manifest_sha256=hashlib.sha256((L/'finalmanifest.json').read_bytes()).hexdigest(),scope='independent verification script; separate sha256sum -c log retained; no independent research reviewer')
(L/'manifest-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
