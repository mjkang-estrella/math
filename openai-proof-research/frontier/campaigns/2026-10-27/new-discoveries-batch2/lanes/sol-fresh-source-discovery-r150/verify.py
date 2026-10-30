import json,hashlib
from pathlib import Path
L=Path(__file__).resolve().parent
out={}
for name in ['finalmanifest.json','scientific-freeze.json']:
 j=json.loads((L/name).read_bytes())
 for e in j['entries']:
  b=(L/e['path']).read_bytes();assert len(b)==e['bytes'] and hashlib.sha256(b).hexdigest()==e['sha256'],e['path']
 out[name]=dict(entries=len(j['entries']),all_pass=True)
assert not (L/'PROOF.md').exists()
(L/'manifest-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(out)
