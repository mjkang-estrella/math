import json,hashlib
from pathlib import Path
D=Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(r)==20 and set(r)==set(map(str,ids))
for i,o in r.items():
 raw=(D/o['raw_local']).read_bytes();q=json.loads(raw);assert raw.endswith(b'\n');assert sha(raw)==o['provenance']['raw_sha256'];assert sha(q['statement'].encode())==o['provenance']['statement_utf8_sha256'];assert q['statement']==o['statement'];assert o['accepted_credit']==0 and o['lean_endpoint'] is None
for f in (D/'sources').glob('*.receipt.json'):
 o=json.loads(f.read_text())
 if o.get('status')==200:assert sha(Path(o['path']).read_bytes())==o['sha256']
pal=json.loads((D/'outputs/pal-bwt-300.json').read_text());assert pal['max_witness_length']==290 and not pal['counterexamples']
part=json.loads((D/'outputs/partition-0-70.json').read_text());assert [q['n'] for q in part]==list(range(71));assert all(q['2']['difference']>=0 and (q['n']<21 or q['3']['difference']>=0) for q in part)
for n in [13,14]:
 f=D/f'outputs/game-{n}-wheel.json';g=D/f'outputs/game-{n}-ferris.json'
 if f.exists() and g.exists():
  a=json.loads(f.read_text());b=json.loads(g.read_text());pred=a['score'][:];pred[0 if a['difference']>0 else 1]-=1;assert pred==b['score']
rep={'entries':20,'excluded':sum(o['outcome'].startswith('excluded') for o in r.values()),'parked':sum(o['outcome'].startswith('parked') for o in r.values()),'accepted_credit':0,'raw_statement_and_source_hashes':'PASS','search_output_consistency':'PASS','limitation':'Validation checks provenance and diagnostic consistency, not formal mathematical semantics.'}
(D/'outputs/validation.json').write_text(json.dumps(rep,indent=2)+'\n');print(rep)
