import pathlib,json,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1]
r=json.loads((D/'outputs/registry-screen.json').read_text());r['complete_scopes']=json.loads((D/'outputs/registry-scopes.json').read_text());r['false_positive_note']='Eger substring hits include words such as integer; no target-specific Lean Pool hit for 340386, Beelen, Ghorpade, or 1809.04690.';r['candidate_340386_search_review']='Repository search returned determinant-related projects; descriptions inspected, none expressly concerned these code weights. No full theorem implication clearance asserted.'
(D/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2))
manifest={}
for p in sorted((D/'sources').rglob('*')):
 if p.is_file():manifest[str(p.relative_to(D))]={'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
(D/'outputs/source-manifest.json').write_text(json.dumps(manifest,indent=2))
# Validate immutable raw-line provenance and exact ID coverage.
x=json.loads((D/'results.json').read_text());reserved=json.loads((D/'reservation.json').read_text())['ids'];assert set(map(int,x))==set(reserved)
for i,v in x.items():
 raw=(D/'raw'/f'{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert hashlib.sha256(raw).hexdigest()==v['provenance']['raw_sha256'];assert hashlib.sha256(v['statement'].encode()).hexdigest()==v['provenance']['statement_utf8_sha256']
logs={p.name:json.loads(p.read_text()) for p in (D/'logs').glob('*.receipt.json')}
assert all(o['returncode']==0 for o in logs.values())
(D/'outputs/validation.json').write_text(json.dumps({'ids':len(x),'raw_hashes':'PASS','statement_hashes':'PASS','process_receipts':logs,'lean':'Not attempted: no credit-qualified strong lead survives.','source_receipt_policy':'Each direct HTTP attempt has a fresh sources subdirectory; no direct HTTP receipt overwritten.'},indent=2))
print('validated',len(x),'IDs;',len(logs),'completed capped processes')
