"""Read-only payload verifier independent of finalize's enumeration code."""
import json,hashlib,datetime
from pathlib import Path
root=Path(__file__).resolve().parent
results={}
for name in ['scientific-freeze.json','finalmanifest.json']:
 doc=json.loads((root/name).read_text());seen=set()
 for rec in doc['records']:
  rel=rec['path'];p=(root/rel).resolve()
  assert p.is_relative_to(root) and rel not in seen and rel!=name
  seen.add(rel);data=p.read_bytes()
  assert len(data)==rec['bytes']
  assert hashlib.file_digest(p.open('rb'),'sha256').hexdigest()==rec['sha256']
 results[name]=len(seen)
 if name=='finalmanifest.json':
  actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-{'finalmanifest.json','manifest-verification.json'}
  assert actual==seen,(actual-seen,seen-actual)
report=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified=results,no_self_hash=True,limits='Computational integrity by separate code; no independent-agent mathematical review.')
(root/'manifest-verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
