import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
out={}
for name in ['scientific-freeze.json','finalmanifest.json']:
 b=(L/name).read_bytes();j=json.loads(b)
 for row in j['entries']:
  raw=(L/row['path']).read_bytes();assert len(raw)==row['bytes'] and sha(raw)==row['sha256'],row['path']
 out[name]=dict(sha256=sha(b),verified_entries=len(j['entries']))
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in {'finalmanifest.json','manifest-verification.json'}}
assert actual=={r['path'] for r in j['entries']}
for row in json.loads((L/'inherited-evidence.json').read_text())['records']:
 assert sha(Path(row['original']).read_bytes())==row['sha256'],row['original']
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
assert sha(guard.read_bytes())=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
out.update(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),all_paths_enumerated=True,guard_unchanged=True,inherited_originals_unchanged=True)
(L/'manifest-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
