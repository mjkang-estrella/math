import pathlib,json,hashlib,datetime,collections
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert set(map(int,r))==set(ids) and len(r)==40
chunks={};source_receipts=0
for i,o in r.items():
 p=o['provenance'];raw=(D/f'raw/{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert sha(raw)==p['raw_sha256'];x=json.loads(raw);assert x['mathdb_id']==int(i) and x['statement']==o['statement'];assert sha(o['statement'].encode())==p['statement_utf8_sha256']
 if p['chunk'] not in chunks:
  b=pathlib.Path(p['chunk']).read_bytes();assert sha(b)==p['chunk_sha256'];chunks[p['chunk']]=b.splitlines(keepends=True)
 assert chunks[p['chunk']][p['line_1based']-1]==raw
 assert o['discovery_credit']==0 and o['lean']['endpoint'] is None
 for s in [o['source_receipt']]+([o['later_source_receipt']] if 'later_source_receipt' in o else []):
  assert s['status']==200 and sha(pathlib.Path(s['path']).read_bytes())==s['sha256'];source_receipts+=1
 if o['search_output']:assert (D/o['search_output']).exists()
for p,h in json.loads((D/'outputs/input-hashes.json').read_text()).items():assert sha(pathlib.Path(p).read_bytes())==h
assert len(json.loads((D/'outputs/search-coverage.json').read_text()))==40
for f in ['graphs','trees','chains','towns','harmonic','q','more','multigraphs','cubic','nahm']:assert (D/f'outputs/{f}.json').exists()
# Manifest excludes itself and validation receipt, which are generated last.
manifest={str(p.relative_to(D)):sha(p.read_bytes()) for p in sorted(D.rglob('*')) if p.is_file() and '__pycache__' not in str(p) and p.name not in ['manifest.json','validation.json']}
(D/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
v=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),entries=40,exact_reserved_keys=True,raw_lines_and_chunk_hashes_verified=True,source_receipt_references_verified=source_receipts,shared_input_hashes_unchanged=True,outcomes=dict(collections.Counter(o['outcome'] for o in r.values())),lean_endpoint_count=0,discovery_credit=0,qualification='bounded investigation; source/checker gaps explicitly retained',manifest_entries=len(manifest))
(D/'outputs/validation.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v,indent=2))
