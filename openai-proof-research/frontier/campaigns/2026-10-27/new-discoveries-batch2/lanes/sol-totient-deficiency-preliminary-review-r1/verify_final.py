from pathlib import Path
import json,hashlib,datetime
p=Path(__file__).resolve().parent
h=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
m=json.loads((p/'finalmanifest.json').read_text())
expected=set(m['files']);actual={str(q.relative_to(p)) for q in p.rglob('*') if q.is_file() and q.name not in m['exclusions']}
errors=[]
if expected!=actual:errors.append('file set mismatch')
for n,v in m['files'].items():
 if h(p/n)!=v:errors.append('manifest hash '+n)
f=json.loads((p/'freeze-before.json').read_text())
for r in f['files']:
 if h(Path(r['original']))!=r['sha256']:errors.append('original '+r['original'])
 if h(p/r['copy'])!=r['sha256']:errors.append('copy '+r['copy'])
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS' if not errors else 'FAIL',manifest_sha256=h(p/'finalmanifest.json'),manifest_files=len(expected),scientific_bindings=len(f['files']),exclusions=m['exclusions'],errors=errors,administrative='snapshot files verified by manifest only; live administrative files deliberately not bound')
(p/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt));assert not errors
