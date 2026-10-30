import hashlib,json,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
j=json.loads((L/'finalmanifest.json').read_text());fail=[]
for r in j['files']:
 p=L/r['path']
 if not p.is_file() or p.stat().st_size!=r['bytes'] or hashlib.sha256(p.read_bytes()).hexdigest()!=r['sha256']:fail.append(r['path'])
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in j['exclusions']}
assert actual=={r['path'] for r in j['files']}
sf=json.loads((L/'scientific-freeze.json').read_text())
for r in sf['files']:
 p=L/r['path'];assert p.stat().st_size==r['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
o=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),entries=len(j['files']),scientific_entries=len(sf['files']),failures=fail,pass_all=not fail,manifest_sha256=hashlib.sha256((L/'finalmanifest.json').read_bytes()).hexdigest())
(L/'manifest-verification.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o));assert not fail
