import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'reservation.json').read_text());o=json.loads((D/'results.json').read_text());assert len(o)==40 and set(o)==set(map(str,r['ids']))
for i,x in o.items():
 raw=(D/f'raw/{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert hashlib.sha256(raw).hexdigest()==x['provenance']['raw_sha256'];assert json.loads(raw)['statement']==x['statement'];assert hashlib.sha256(x['statement'].encode()).hexdigest()==x['provenance']['statement_utf8_sha256'];assert x['discovery_credit']==0
for i in ['376562','376563']:
 a=json.loads((D/'outputs/weighted-loop.json').read_text())[i];assert all(x['max_equal'] and x['sum_equal'] for x in a['rows'])
assert json.loads((D/'outputs/tree-deep.json').read_text())['violations']==[]
assert not list(D.glob('**/*.olean')) and not list(D.glob('**/*.lean'))[1:] # only fetched upstream Lean; no new endpoint
runs={p.name:json.loads(p.read_text()) for p in (D/'logs').glob('*.receipt.json')}
manifest={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (D/'sources').iterdir() if p.is_file()};(D/'outputs/source-manifest.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sha256':manifest},indent=2)+'\n')
(D/'outputs/validation.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reserved_records':40,'raw_line_and_statement_hashes':'PASS','numerical_diagnostics':'only; no formal proof','lean_endpoint':None,'accepted_credit':0,'campaign_count_changed':False,'runs':runs},indent=2)+'\n');print('PASS: exactly40 reserved records, raw lines and hashes; no new Lean endpoint')
