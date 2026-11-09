import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text());ids=set(json.loads((D/'reservation.json').read_text())['ids']);assert len(r)==20 and set(map(int,r))==ids
sha=lambda b:hashlib.sha256(b).hexdigest()
for k,o in r.items():
 raw=(D/f'raw/{k}.jsonl').read_bytes();assert raw.endswith(b'\n');assert sha(raw)==o['provenance']['raw_sha256'];assert sha(o['statement'].encode())==o['provenance']['statement_utf8_sha256'];assert json.loads(raw)['mathdb_id']==int(k);assert o['credit_claimed']==0
for p in (D/'sources').glob('*.receipt.json'):
 o=json.loads(p.read_text())
 if o.get('status')==200:assert sha(pathlib.Path(o['path']).read_bytes())==o['sha256']
assert all(o['returncode']==0 for p in (D/'logs').glob('*.receipt.json') if (o:=json.loads(p.read_text())) and p.stem.split('.')[0] in ['sparse','cyclic','lens','apn','apn-scalar','kassami','kassami-closure','hilbert-adam','reducts'])
manifest=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name not in ['artifact-manifest.json','validation.json'] and 'tmp' not in p.relative_to(D).parts and not (p.parent.name=='logs' and p.name.startswith('validation')):
  manifest.append(dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())))
(D/'outputs/artifact-manifest.json').write_text(json.dumps(manifest,indent=2))
o=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),reserved_ids=20,result_keys=20,raw_newline_hashes_verified=20,successful_http_receipts_verified=True,full_literal_endpoints=0,lean_packet=False,root_acceptance=False,artifact_count=len(manifest));(D/'outputs/validation.json').write_text(json.dumps(o,indent=2));print(o)
