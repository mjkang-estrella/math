import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def verify(name):
 j=json.loads((L/name).read_bytes())
 for r in j['records']:
  b=(L/r['path']).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes'],r['path']
 return len(j['records'])
# Independent scientific and original-copy check, no mutable live administrative context.
n=verify('scientific-freeze.json');originals=json.loads((L/'original-copy-provenance.json').read_bytes())
for r in originals:
 a=(R/r['original']).read_bytes();b=(L/r['copy']).read_bytes()
 assert a==b and sha(b)==r['sha256']
guard=json.loads((L/'guard-binding.json').read_bytes());assert sha(Path(guard['path']).read_bytes())==guard['sha256']
(L/'scientific-verification.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',scientific=n,originals=len(originals),live_admin='not compared; archived snapshots only'),indent=2)+'\n')
m=verify('finalmanifest.json');j=json.loads((L/'finalmanifest.json').read_bytes())
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(j['exclusions'])
assert actual=={r['path'] for r in j['records']}
(L/'manifest-verification.json').write_text(json.dumps(dict(status='PASS',manifest=m,explicit_exclusions=j['exclusions'],exact_file_set=True),indent=2)+'\n')
print('PASS scientific',n,'originals',len(originals),'manifest',m,'exact file set; explicit self/receipt exclusions')
