import pathlib,json,hashlib,datetime,collections
P=pathlib.Path(__file__).resolve().parents[1];h=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((P/'results.json').read_text());ids=json.loads((P/'reservation.json').read_text())['ids'];assert len(r)==40 and set(r)==set(map(str,ids))
for i,d in r.items():
 raw=(P/'raw'/f'{i}.jsonl').read_bytes();assert raw.endswith(b'\n') and h(raw)==d['provenance']['raw_line_sha256'];assert h(d['literal_statement'].encode())==d['provenance']['statement_utf8_sha256'];assert json.loads(raw)['statement']==d['literal_statement'];assert d['accepted_credit']==0
for f in (P/'receipts').glob('*.json'):
 d=json.loads(f.read_text())
 if d.get('status')==200:assert h(pathlib.Path(d['file']).read_bytes())==d['sha256']
counts=collections.Counter(d['outcome'] for d in r.values());report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'entries':len(r),'provenance_and_receipt_hashes':'passed','credit':0,'outcomes':counts,'lean_endpoint':None,'no_lean_replay_claim':True}
(P/'outputs/validation.json').write_text(json.dumps(report,indent=2)+'\n')
manifest={str(f.relative_to(P)):h(f.read_bytes()) for f in sorted(P.rglob('*')) if f.is_file() and f.name!='manifest.json' and '__pycache__' not in str(f)};(P/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(report,indent=2))
