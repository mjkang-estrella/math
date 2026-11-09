import json,pathlib,hashlib
L=pathlib.Path(__file__).resolve().parents[1]
r=json.loads((L/'results.json').read_text());reserved=json.loads((L/'reservation.json').read_text())['ids'];assert set(map(int,r))==set(reserved) and len(r)==20
for k,e in r.items():
 b=(L/'raw'/f'{k}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==e['provenance']['raw_sha256'];assert e['credit']==0 and e['lean_endpoint'] is None
for name in ['SUMMARY.md','CANDIDATE.md']:assert (L/name).stat().st_size>0
for name,e in json.loads((L/'outputs/receipt-manifest.json').read_text()).items():assert hashlib.sha256((L/name).read_bytes()).hexdigest()==e['sha256']
print('PASS: 20 reserved ID keys, exact raw hashes/newlines, zero credit, required reports, receipt hashes.')
