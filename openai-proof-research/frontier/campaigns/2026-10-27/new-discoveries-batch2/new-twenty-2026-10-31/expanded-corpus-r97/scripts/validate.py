import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
R=json.loads((D/'results.json').read_text());ids=set(map(str,json.loads((D/'reservation.json').read_text())['ids']));assert len(R)==20 and set(R)==ids
for i,r in R.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n') and sha(b)==r['provenance']['raw_sha256'];o=json.loads(b);assert o['statement']==r['statement'];assert sha(r['statement'].encode())==r['provenance']['statement_utf8_sha256'];assert r['discovery_credit']==0 and r['lean_endpoint'] is None
 rec=json.loads((D/r['source_receipt']).read_text());assert rec['status']==200;assert sha(pathlib.Path(rec['path']).read_bytes())==rec['sha256']==r['source_body_sha256']
manifest={str(p.relative_to(D)):sha(p.read_bytes()) for p in D.rglob('*') if p.is_file() and '__pycache__' not in str(p) and p.name not in ['manifest.json','validation.json'] and not str(p).endswith('logs/validate.log')}
(D/'outputs/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');(D/'outputs/validation.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reserved_keys_exactly20':True,'raw_and_source_hashes':'PASS','credit':0,'lean':'absent; no endpoint claimed','completion':'partial; five finite invariant searches and formalization remain','manifest_files':len(manifest)},indent=2)+'\n');print('PASS:20 exact keys, raw bytes and source hashes; scientific completion explicitly partial')
