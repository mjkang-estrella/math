from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'final-manifest.json').read_text());expected={r['path'] for r in m['files']};actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json']}
assert actual==expected
for r in m['files']:assert sha(L/r['path'])==r['sha256']
bindings=[json.loads(s) for s in (L/'bindings.jsonl').read_text().splitlines()]
for r in bindings:assert sha(Path(r['original']))==r['sha256']==sha(Path(r['copy']))
refs=json.loads((L/'history-verified.json').read_text())
for r in refs:assert sha(Path(r['path']))==r['sha256']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'final-manifest.json'),files_verified=len(m['files']),source_bindings_verified=len(bindings),immutable_history_verified=len(refs),administrative_snapshots='verified as manifest bytes only, not against moving originals',counts='9 additional /39 total /next40; root alone accepts',limitations='No current registry HEAD; mathematical universal lead incomplete; no discovery acceptance')
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
