"""Separate read-only payload verifier; writes only its excluded local receipt."""
from pathlib import Path
import hashlib,json,datetime
root=Path(__file__).resolve().parent
manifest=json.loads((root/'finalmanifest.json').read_text())
fail=[];names=set()
for row in manifest['records']:
 name=row['path'];names.add(name);p=root/name
 if not p.is_file():fail.append([name,'missing']);continue
 data=p.read_bytes()
 if len(data)!=row['bytes'] or hashlib.sha256(data).hexdigest()!=row['sha256']:fail.append([name,'bytes/hash'])
actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
assert actual-names==set(manifest['excluded'][:1]) or actual-names==set(manifest['excluded']), actual-names
science=json.loads((root/'scientific-freeze.json').read_text())
for row in science['records']:
 data=(root/row['path']).read_bytes()
 if hashlib.sha256(data).hexdigest()!=row['sha256'] or len(data)!=row['bytes']:fail.append([row['path'],'science'])
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),pass_=not fail,manifest_entries=len(names),scientific_entries=len(science['records']),failures=fail,selfhash_excluded=True,live_context_compared=False)
(root/'manifest-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out));assert not fail
