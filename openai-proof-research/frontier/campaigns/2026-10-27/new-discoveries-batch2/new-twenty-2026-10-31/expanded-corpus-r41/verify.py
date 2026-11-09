import pathlib,json,hashlib
p=pathlib.Path(__file__).resolve().parent;r=json.loads((p/'reservation.json').read_text());d=json.loads((p/'results.json').read_text());assert len(d)==40 and set(map(int,d))==set(r['ids'])
manifest=p.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/manifest.json';m=json.loads(manifest.read_text());ms=json.dumps(m);chunks={}
for k,v in d.items():
 raw=(p/v['raw_local']).read_bytes();assert raw.endswith(b'\n');assert hashlib.sha256(raw).hexdigest()==v['provenance']['raw_sha256'];o=json.loads(raw);assert o['statement']==v['literal_statement'];assert hashlib.sha256(o['statement'].encode()).hexdigest()==v['provenance']['statement_sha256']
 f=pathlib.Path(v['provenance']['chunk']);
 if str(f) not in chunks:
  b=f.read_bytes();h=hashlib.sha256(b).hexdigest();assert h==v['provenance']['chunk_sha256'] and h in ms;chunks[str(f)]=b.splitlines(keepends=True)
 assert chunks[str(f)][v['provenance']['line_one_based']-1]==raw;assert v['accepted_credit']==0 and v['lean_endpoint'] is None
assert len(json.loads((p/'leaf-independent.json').read_text())['catalog'])==256
art={str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(p.rglob('*')) if f.is_file() and f.name not in ['artifact-sha256.json','verification.json']}
(p/'artifact-sha256.json').write_text(json.dumps(art,indent=2));(p/'verification.json').write_text(json.dumps({'forty_ids':True,'raw_hashes_and_lines':True,'statement_hashes':True,'manifest_bound_chunks':True,'credit':0,'literal_lean_endpoint':False,'artifacts_hashed':len(art)},indent=2));print('PASS provenance and40 dispositions; no Lean endpoint claimed')
