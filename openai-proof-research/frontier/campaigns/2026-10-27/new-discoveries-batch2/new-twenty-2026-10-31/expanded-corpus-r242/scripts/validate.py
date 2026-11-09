import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
R=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids']
assert set(R)==set(map(str,ids)) and len(R)==20
for k,r in R.items():
 raw=(D/f'raw/{k}.jsonl').read_bytes();assert raw.endswith(b'\n')
 assert sha(raw)==r['provenance']['raw_sha256'];assert json.loads(raw)['statement']==r['statement'];assert sha(r['statement'].encode())==r['provenance']['statement_utf8_sha256']
 assert r['lean_endpoint'] is None and r['credit_claimed']==0
 for f in r['evidence_files']:assert (D/f).exists() or (D/'sources'/f).exists(),f
for p in (D/'sources').glob('*.receipt.json'):
 r=json.loads(p.read_text());b=p.with_name(p.name.replace('.receipt.json','.body'))
 if 'sha256' in r:assert sha(b.read_bytes())==r['sha256'],p
for name in ['SUMMARY.md','CANDIDATE.md','results.json']:assert (D/name).stat().st_size>0
assert not list(D.rglob('__pycache__'))
files={str(p.relative_to(D)):sha(p.read_bytes()) for p in D.rglob('*') if p.is_file() and p.name not in ['artifact-sha256.json','validation.json']}
(D/'artifact-sha256.json').write_text(json.dumps(files,indent=2)+'\n')
(D/'validation.json').write_text(json.dumps({'status':'pass','results':20,'raw_hashes_match':True,'http_body_hashes_match':True,'credit':0,'lean_endpoints':0,'scope':'artifact and diagnostic integrity, not mathematical proof or novelty certification'},indent=2)+'\n');print('PASS: 20 IDs; raw and HTTP body hashes; evidence paths; deliverables; no bytecode.')
