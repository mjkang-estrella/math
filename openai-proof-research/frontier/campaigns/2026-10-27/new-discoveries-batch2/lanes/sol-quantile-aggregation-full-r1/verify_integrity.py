from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text())
assert 'manifest.json' not in m and 'verification-receipt.json' not in m
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
assert actual==set(m)
for rel,h in m.items():assert sha(L/rel)==h,rel
for r in json.loads((L/'freeze.json').read_text()):
 assert sha(Path(r['original']))==r['sha256'],r['original']
 assert sha(L/r['copy'])==r['sha256'],r['copy']
for line in (L/'http.jsonl').read_text().splitlines():
 r=json.loads(line)
 if 'sha256' in r:assert sha(L/r['path'])==r['sha256']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'manifest.json'),files_verified=len(m),frozen_originals_and_copies_verified=True,http_bodies_verified=True,administrative_policy='snapshot only',excluded=['manifest.json','verification-receipt.json'])
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))
