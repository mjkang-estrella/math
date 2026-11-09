import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text());x=json.loads((D/'reservation.json').read_text())
assert len(r)==40 and set(r)==set(map(str,x['ids']))
for k,o in r.items():
 raw=(D/f'raw/{k}.jsonl').read_bytes();p=o['provenance'];assert raw.endswith(b'\n')
 assert hashlib.sha256(raw).hexdigest()==p['raw_sha256'];assert hashlib.sha256(o['statement'].encode()).hexdigest()==p['statement_utf8_sha256']
 assert json.loads(raw)['statement']==o['statement'];assert o['credit']==0
 source=D/o['source_text_file'];assert source.exists();assert hashlib.sha256(source.read_bytes()).hexdigest()==o['source_text_sha256']
for p in (D/'sources').glob('*.receipt.json'):
 o=json.loads(p.read_text())
 if o.get('status')==200:
  data=pathlib.Path(o['path']).read_bytes();assert hashlib.sha256(data).hexdigest()==o['sha256']
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'entries':len(r),'raw_line_statement_source_receipt_hashes':'pass','credit':0,'lean_endpoint':False,'full_upstream_rebuild':False}
(D/'outputs/validation.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
