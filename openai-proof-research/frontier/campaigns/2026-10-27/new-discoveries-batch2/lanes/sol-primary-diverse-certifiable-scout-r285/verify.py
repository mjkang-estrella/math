from research import *
manifest=json.loads((L/'MANIFEST.json').read_text());n=0
for r in manifest['files']:
 p=L/r['path'];d=p.read_bytes();assert len(d)==r['bytes'] and sha(d)==r['sha256'],str(p);n+=1
for line in (L/'bindings.jsonl').read_text().splitlines():
 r=json.loads(line);p=L/r['path'];assert sha(p.read_bytes())==r['sha256'],str(p)
refs=json.loads((L/'duplicate-filter-bindings.json').read_text())
for r in refs:
 p=pathlib.Path(r['original']);d=p.read_bytes();assert sha(d)==r['sha256'] and len(d)==r['bytes'],str(p)
for r in json.loads((L/'administrative-snapshot.json').read_text()):
 assert sha((L/r['snapshot']).read_bytes())==r['sha256']
receipt=dict(status='PASS',manifest_sha256=sha((L/'MANIFEST.json').read_bytes()),manifest_files=n,scientific_original_references_verified=len(refs),source_binding_hashes='PASS',administrative_snapshots='PASS (original administrative state deliberately not compared)',time=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),separate_guarded_process=True)
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))
