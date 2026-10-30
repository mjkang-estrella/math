from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
counts={}
for n in ['scientific-freeze.json','finalmanifest.json']:
 j=json.loads((L/n).read_text())
 for path,r in j['records'].items():
  p=L/path
  assert p.stat().st_size==r['bytes'],path
  assert digest(p)==r['sha256'],path
 counts[n]=len(j['records'])
j=json.loads((L/'primary-hashes.json').read_text())
for p,h in j.items():assert digest(L/p)==h,p
binding=json.loads((L/'guard-binding.json').read_text())
assert digest(Path(binding['path']))==binding['sha256']
manifest=json.loads((L/'finalmanifest.json').read_text())
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(manifest['excludes'])
assert actual==set(manifest['records'])
result=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',counts=counts,primary_files=len(j),finalmanifest_sha256=digest(L/'finalmanifest.json'),scope='Independent verifier implementation, same solo researcher; integrity only, not independent mathematical review.')
(L/'manifest-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
