import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(r)==40 and set(map(int,r))==set(ids)
for i,o in r.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==o['provenance']['raw_sha256'];assert json.loads(b)['statement']==o['statement'];assert hashlib.sha256(o['statement'].encode()).hexdigest()==o['provenance']['statement_utf8_sha256'];assert o['accepted_credit']==0 and o['lean_endpoint'] is None
for f in (D/'sources').glob('*.receipt.json'):
 o=json.loads(f.read_text())
 if 'sha256' in o:assert hashlib.sha256(pathlib.Path(o['path']).read_bytes()).hexdigest()==o['sha256']
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'entries':40,'raw_lines_newline_hash_and_statement_checks':'pass','retrieved_http_body_hash_checks':'pass','lean_claim':False,'completion_claim':False,'credit':0}
(D/'outputs/validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
