from pathlib import Path
import json,hashlib,ast,datetime,os
D=Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((D/'reservation.json').read_text());x=json.loads((D/'results.json').read_text());assert set(x)=={str(i) for i in r['ids']};assert len(x)==20
for i,o in x.items():
 raw=(D/o['raw_local']).read_bytes();assert raw.endswith(b'\n');assert sha(raw)==o['provenance']['raw_sha256'];a=json.loads(raw);assert a['mathdb_id']==int(i);assert a['statement']==o['statement'];assert sha(a['statement'].encode())==o['provenance']['statement_utf8_sha256'];assert o['accepted_credit']==0 and o['lean_endpoint'] is None
 assert sha((D/o['source']['local']).read_bytes())==o['source']['sha256']
checked=0
for p in (D/'sources').glob('*.receipt.json'):
 a=json.loads(p.read_text())
 if a.get('status')==200:assert sha(Path(a['path']).read_bytes())==a['sha256'];checked+=1
for p in (D/'scripts').glob('*.py'):ast.parse(p.read_text())
# Inventory, not a CPU-time claim. Wall-capped process records are retained as produced.
receipts={p.stem:json.loads(p.read_text()) for p in (D/'logs').glob('*.receipt.json')}
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reserved_ids':20,'results_ids':20,'raw_newline_and_hash_checks':20,'source_binding_checks':20,'successful_http_receipts_verified':checked,'python_syntax':'all local scripts parsed','resource_receipts':receipts,'credit':0,'lean_packet':None,'limitations':'No endpoint, no general semantic certification of numerical scripts; full finite-search requirement has unresolved gates.'}
(D/'outputs/validation.json').write_text(json.dumps(out,indent=2)+'\n')
manifest={str(p.relative_to(D)):sha(p.read_bytes()) for p in D.rglob('*') if p.is_file() and p.name!='manifest.json' and '__pycache__' not in str(p)}
(D/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'ids':20,'HTTP_receipts':checked,'manifest_files':len(manifest),'credit':0}))
