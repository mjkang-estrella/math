from pathlib import Path
import json,hashlib,datetime
p=Path(__file__).parent
h=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
m=json.loads((p/'final-manifest.json').read_text());errors=[]
for r in m['files']:
 q=p/r['path']
 if not q.is_file() or h(q)!=r['sha256']:errors.append(r['path'])
expected={r['path'] for r in m['files']}
actual={str(q.relative_to(p)) for q in p.rglob('*') if q.is_file()}-set(m['excluded'])
if expected!=actual:errors.append('inventory mismatch')
f=json.loads((p/'freeze-before.json').read_text())
for r in f['scientific']:
 for q in [Path(r['original']),p/r['copy']]:
  if not q.is_file() or h(q)!=r['sha256']:errors.append(str(q))
r=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS' if not errors else 'FAIL',manifest_sha256=h(p/'final-manifest.json'),manifest_files=len(expected),scientific_original_copy_pairs=len(f['scientific']),errors=errors,excluded=m['excluded'],policy='Manifest excludes itself and this receipt explicitly. Administrative live paths are not verified or scientific inputs.')
(p/'manifest-verification.json').write_text(json.dumps(r,indent=2));print(json.dumps(r));assert not errors
