from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
m=json.loads((L/'finalmanifest.json').read_bytes());s=json.loads((L/'scientific-freeze.json').read_bytes())
for p,d in m['entries'].items():
 b=(L/p).read_bytes();assert len(b)==d['bytes'] and sha(b)==d['sha256'],p
for p,h in s['entries'].items():assert sha((L/p).read_bytes())==h,p
j=dict(manifest_entries=len(m['entries']),scientific_entries=len(s['entries']),manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),scientific_freeze_sha256=sha((L/'scientific-freeze.json').read_bytes()),verified=True)
(L/'manifest-verification.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j))
