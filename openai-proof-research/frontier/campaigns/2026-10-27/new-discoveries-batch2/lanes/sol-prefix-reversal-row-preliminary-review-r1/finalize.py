import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parent.parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
f=B/'lanes/root-r169-preliminary-freeze-r1/review-freeze.json'
g=B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
before=json.loads((L/'before.json').read_text())
assert h(f)==before['freeze_sha256']
assert h(g)=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
for r in before['files']:
 for p in [Path(r['path']),L/r['copy']]:assert h(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
(L/'after.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),originals=84,copies=84,all_unchanged=True,freeze_sha256=h(f),guard_sha256=h(g)),indent=2))
records=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','verified-manifest.json']:
  records.append(dict(path=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=h(p)))
(L/'manifest.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=records),indent=2))
print('after freeze PASS; manifest',len(records),'files')
