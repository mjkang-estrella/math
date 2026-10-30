import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
verified={}
for n in ['scientific-freeze.json','finalmanifest.json']:
 j=json.loads((L/n).read_text());names=[]
 for r in j['records']:
  p=L/r['path'];assert p.is_file(),r['path'];b=p.read_bytes()
  assert sha(b)==r['sha256'] and len(b)==r['bytes'],r['path'];names.append(r['path'])
 assert len(set(names))==len(names)
 verified[n]=len(names)
 if n=='finalmanifest.json':
  actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in j['exclude']}
  assert actual==set(names),(actual-set(names),set(names)-actual)
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',verified=verified,finalmanifest_sha256=sha((L/'finalmanifest.json').read_bytes()),scientific_freeze_sha256=sha((L/'scientific-freeze.json').read_bytes()),self_hash=False,scope='Independent recomputation of final payload and scientific hashes. No mutable shared context checked as invariant.')
(L/'manifest-verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
