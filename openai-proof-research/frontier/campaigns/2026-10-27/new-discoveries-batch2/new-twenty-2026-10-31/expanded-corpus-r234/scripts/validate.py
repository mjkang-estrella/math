import pathlib,json,hashlib,re,collections
D=pathlib.Path(__file__).resolve().parents[1]
r=json.loads((D/'results.json').read_text());reservation=json.loads((D/'reservation.json').read_text());assert set(r)==set(map(str,reservation['ids'])) and len(r)==20
for i,o in r.items():
 raw=(D/'raw'/f'{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert hashlib.sha256(raw).hexdigest()==o['provenance']['raw_sha256'];assert hashlib.sha256(o['statement'].encode()).hexdigest()==o['provenance']['statement_utf8_sha256']
for p in (D/'sources').glob('*.receipt.json'):
 o=json.loads(p.read_text());b=p.with_name(p.name.replace('.receipt.json','.body'))
 if 'sha256' in o:assert b.exists() and hashlib.sha256(b.read_bytes()).hexdigest()==o['sha256'],p
assert json.loads((D/'replay-result.json').read_text())['status']=='PASS'
for name in ['fresh2-build','fresh2-inventory','fresh2-axioms','fresh2-checker']:
 assert json.loads((D/'logs'/f'{name}.receipt.json').read_text())['returncode']==0
assert len(re.findall(r'^LOCAL ',(D/'logs/fresh2-inventory.log').read_text(),re.M))==13
assert not list(D.rglob('*.pyc')) and not list(D.rglob('__pycache__'))
manifest={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(D.rglob('*')) if p.is_file() and p.name!='artifact-sha256.json'}
(D/'artifact-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
(D/'validation.json').write_text(json.dumps({'status':'PASS','records':20,'raw_lines_with_newlines':20,'all_http_body_hashes_match':True,'strict_fresh_lean_and_checker':'PASS','local_declarations':13,'accepted_credit':0,'candidate_ids':[356266]},indent=2)+'\n')
print('PASS: 20 exact record entries, 20 raw line hashes, HTTP receipt hashes, fresh Lean replay, 13 audited declarations')
