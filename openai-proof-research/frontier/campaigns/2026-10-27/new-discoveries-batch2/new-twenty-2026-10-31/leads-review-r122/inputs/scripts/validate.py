import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text());reservation=json.loads((D/'reservation.json').read_text())
assert set(r)==set(map(str,reservation['ids'])) and len(r)==20
for i,o in r.items():
 raw=(D/f'raw/{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert hashlib.sha256(raw).hexdigest()==o['provenance']['raw_sha256'];assert hashlib.sha256(o['statement'].encode()).hexdigest()==o['provenance']['statement_utf8_sha256']
 for s in o['sources']:assert hashlib.sha256((D/s['path']).read_bytes()).hexdigest()==s['sha256']
assert (D/'SUMMARY.md').exists()
from collections import Counter
print('20 exact reserved IDs; raw/statement/source hashes verified; summary exists; outcomes:',dict(Counter(o['outcome'] for o in r.values())))
exclude={'manifest.json','validate-final.log','validate-final.receipt.json'}
manifest={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in D.rglob('*') if p.is_file() and p.name not in exclude}
(D/'manifest.json').write_text(json.dumps({'hashes':manifest,'limitation':'manifest excludes itself and active final validation log/receipt'},indent=2)+'\n')
