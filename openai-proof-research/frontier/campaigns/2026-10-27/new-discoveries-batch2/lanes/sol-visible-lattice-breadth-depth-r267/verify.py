from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'final-manifest.json').read_text());fail=[]
for r in m['files']:
 p=L/r['path']
 if not p.is_file() or p.stat().st_size!=r['bytes'] or sha(p)!=r['sha256']:fail.append(r['path'])
expected={r['path'] for r in m['files']}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excludes']}
if actual!=expected:fail.append('file inventory mismatch')
for r in json.loads((L/'bindings.json').read_text())['items']+json.loads((L/'history-bindings.json').read_text()):
 if sha(L/r['copy'])!=r['sha256']:fail.append(r['copy'])
 if r['category']=='frozen' and sha(Path(r['original']))!=r['sha256']:fail.append(r['original'])
assert not (L/'PROOF.md').exists()
r={'status':'PASS' if not fail else 'FAIL','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(L/'final-manifest.json'),'checked_files':len(m['files']),'failures':fail,'separate_guarded_verification':True}
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2));print(json.dumps(r));assert not fail
