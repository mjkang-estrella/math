import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text());reserved=json.loads((D/'reservation.json').read_text())['ids'];h=lambda b:hashlib.sha256(b).hexdigest()
assert len(r)==20 and set(map(int,r))==set(reserved)
for k,o in r.items():
 raw=(D/f'raw/{k}.jsonl').read_bytes();assert raw.endswith(b'\n');assert h(raw)==o['provenance']['raw_sha256'];assert json.loads(raw)['statement']==o['statement'];assert h(o['statement'].encode())==o['provenance']['statement_utf8_sha256'];assert o['credit']==0 and o['literal_lean_endpoint'] is None
receipts=[]
for p in sorted((D/'sources').glob('*.receipt.json')):
 o=json.loads(p.read_text());q=o.get('path')
 if q:assert h(pathlib.Path(q).read_bytes())==o['sha256']
 receipts.append({'file':str(p.relative_to(D)),'status':o.get('status'),'error':o.get('error')})
logs=[]
for p in sorted((D/'logs').glob('*.receipt.json')):
 o=json.loads(p.read_text());logs.append({'file':str(p.relative_to(D)),**o})
for f in ['SUMMARY.md','CANDIDATE.md','ROUTES.md']:assert (D/f).stat().st_size>100
assert not list(D.rglob('__pycache__'))
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reserved_entries':20,'all_raw_line_hashes_and_statement_hashes_valid':True,'http_receipt_hashes_valid':True,'network_failures':[x for x in receipts if x['status']!=200],'process_receipts':logs,'no_lean_endpoint_claimed':True,'credit':0,'limits':'Source chunk hashes were computed during extraction; validation checks stored raw line bytes and statement hashes, not a fresh second full corpus hash.'}
(D/'validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'entries':20,'http_receipts':len(receipts),'network_failures':out['network_failures'],'process_receipts':len(logs),'result':'PASS'}))
