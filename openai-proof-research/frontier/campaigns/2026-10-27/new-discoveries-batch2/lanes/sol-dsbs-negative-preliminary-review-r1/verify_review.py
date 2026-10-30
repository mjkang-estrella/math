from pathlib import Path
import json,hashlib,datetime
p=Path(__file__).resolve().parent
m=json.loads((p/'finalmanifest.json').read_text())
listed={r['path'] for r in m['files']}
actual={str(f.relative_to(p)) for f in p.rglob('*') if f.is_file()}-{'finalmanifest.json','finalmanifest-verification.json'}
assert actual==listed,(actual-listed,listed-actual)
for r in m['files']:
 f=p/r['path'];assert f.stat().st_size==r['bytes'];assert hashlib.sha256(f.read_bytes()).hexdigest()==r['sha256']
before=json.loads((p/'before-hashes.json').read_text())
for r in before['files']:
 f=Path(r['path']);assert hashlib.sha256(f.read_bytes()).hexdigest()==r['sha256']
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_payload_files':len(listed),'manifest_sha256':hashlib.sha256((p/'finalmanifest.json').read_bytes()).hexdigest(),'originals_rechecked':len(before['files']),'scope':'all review payload paths independently enumerated and hashed; manifest and this receipt excluded from own payload list'}
(p/'finalmanifest-verification.json').write_text(json.dumps(receipt,indent=2))
print(json.dumps(receipt))
