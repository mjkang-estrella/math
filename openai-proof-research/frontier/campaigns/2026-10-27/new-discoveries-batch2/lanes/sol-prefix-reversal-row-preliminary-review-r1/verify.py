import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parent.parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
d=json.loads((L/'manifest.json').read_text())
for r in d['files']:
 p=L/r['path'];assert h(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
assert {r['path'] for r in d['files']}=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verified-manifest.json']}
before=json.loads((L/'before.json').read_text())
assert len(before['files'])==84
assert h(B/'lanes/root-r169-preliminary-freeze-r1/review-freeze.json')==before['freeze_sha256']
assert h(B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
for r in before['files']:
 for p in [Path(r['path']),L/r['copy']]:assert h(p)==r['sha256'] and p.stat().st_size==r['bytes']
for name in ['checks.json','route-checks.json']:
 assert (L/'replay'/name).read_bytes()==(L/'inputs/lanes/sol-fresh-source-discovery-r169'/name).read_bytes()
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS integrity only',files=len(d['files']),originals=84,copies=84,manifest_sha256=h(L/'manifest.json'),review_sha256=h(L/'review.md'),verdict='SOURCE PASS / MATH PASS classical / SUBSTANTIVE EXCLUDE / NOVELTY HOLD / formal feasibility UNESTABLISHED',credit=0)
(L/'verified-manifest.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))
