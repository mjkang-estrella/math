import hashlib,json
from pathlib import Path
L=Path(__file__).resolve().parent
for name in ['scientific-freeze.json','finalmanifest.json']:
 j=json.loads((L/name).read_text())
 for r in j['files']:
  p=L/r['path'];b=p.read_bytes();assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'],r['path']
 print(name,len(j['files']),'paths verified')
assert not (L/'PROOF.md').exists()
print('No PROOF.md; full source claim remains unresolved')
