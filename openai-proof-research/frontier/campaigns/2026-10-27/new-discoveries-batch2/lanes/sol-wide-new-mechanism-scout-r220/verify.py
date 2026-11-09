from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'finalmanifest.json').read_text());excluded={'finalmanifest.json','verification-receipt.json'}
assert set(m)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in excluded}
for name,h in m.items():assert sha(L/name)==h,name
for r in json.loads((L/'freeze.json').read_text()):
 assert sha(Path(r['copy']))==r['sha256']
 if r['kind']=='scientific frozen':assert sha(Path(r['path']))==r['sha256']
refs=json.loads((L/'frozen/history-index.json').read_text())['records']
for r in refs:assert sha(Path(r['snapshot_reference']))==r['sha256']
for s in (L/'http.jsonl').read_text().splitlines():
 r=json.loads(s)
 if 'path' in r:assert sha(Path(r['path']))==r['sha256']
p=json.loads((L/'provenance.json').read_text());assert sha(Path(p['guard']['path']))==p['guard']['sha256']
assert json.loads((L/'checks.json').read_text())['exit']==0
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':len(m),'immutable_history_references':len(refs),'manifest_sha256':sha(L/'finalmanifest.json'),'source_and_coordination_bindings':'PASS','administrative':'snapshots only','count_credit_requested':0,'no_priority_or_acceptance_claim':True}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))
