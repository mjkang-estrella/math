import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(r)==20 and set(map(int,r))==set(ids)
for k,o in r.items():
 b=(D/f'raw/{k}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==o['provenance']['raw_sha256'];assert hashlib.sha256(o['statement'].encode()).hexdigest()==o['provenance']['statement_utf8_sha256'];assert o['credit']==0 and o['lean_endpoint'] is None
 assert json.loads((D/o['primary_source_receipt']).read_text())['sha256']==o['primary_source_sha256']
meta={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'entries':20,'all_raw_and_statement_hashes_verified':True,'source_hashes_verified':True,'formal_endpoints':0,'qualification':'partial bounded pass; see explicit gaps','files':{}}
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name not in ['validation.json'] and '__pycache__' not in str(p):meta['files'][str(p.relative_to(D))]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
(D/'outputs/validation.json').write_text(json.dumps(meta,indent=2)+'\n');print('PASS:20 IDs, raw newlines, hashes, source receipts, zero claimed endpoints;',len(meta['files']),'files inventoried')
