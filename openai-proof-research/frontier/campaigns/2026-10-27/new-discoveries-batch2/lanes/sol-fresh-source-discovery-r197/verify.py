from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent; R=L.parents[5]
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'finalmanifest.json').read_text());errors=[]
for n,d in manifest['files'].items():
 p=L/n
 if not p.is_file() or h(p)!=d:errors.append(['manifest',n])
ex=set(manifest['excludes']);actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in ex}
if actual!=set(manifest['files']):errors.append(['manifest inventory',sorted(actual-set(manifest['files'])),sorted(set(manifest['files'])-actual)])
rows=json.loads((L/'input-bindings.json').read_text())+json.loads((L/'scientific-input-freeze.json').read_text())['bindings']
for orig,copy,d,z in rows:
 p=Path(orig)
 if not p.is_absolute():p=R/p
 c=L/copy
 if not p.is_file() or not c.is_file() or h(p)!=d or h(c)!=d or p.stat().st_size!=z or c.stat().st_size!=z:errors.append(['original/copy',orig,copy])
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS' if not errors else 'FAIL',manifest_sha256=h(L/'finalmanifest.json'),manifest_files=len(manifest['files']),original_copy_bindings=len(rows),excludes=sorted(ex),errors=errors,administrative_live_binding=False,limits='Integrity only; no mathematical novelty/source-resolution certification. Guard RSS sampling does not rule out unsampled transients.')
(L/'manifest-verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2));assert not errors
