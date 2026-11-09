import pathlib,json,hashlib,resource,collections,datetime
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
w=pathlib.Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((w/'reservation.json').read_text());d=json.loads((w/'results.json').read_text());assert len(d)==40 and set(map(int,d))==set(map(int,r['ids']))
manifest_path=next(pathlib.Path(p) for p in r['input_hashes'] if p.endswith('r301/manifest.json'));manifest=json.loads(manifest_path.read_text()); entries={x['path']:x for x in manifest['files']}
chunks={}
for k,x in d.items():
 p=x['provenance'];chunk=pathlib.Path(p['chunk']).resolve();name=str(chunk.relative_to(manifest_path.parent));assert name in entries
 if str(chunk) not in chunks:
  raw=chunk.read_bytes();assert h(raw)==p['chunk_sha256']==entries[name]['sha256'];chunks[str(chunk)]=raw.splitlines(keepends=True)
 raw=chunks[str(chunk)][p['one_based_line']-1];assert raw.endswith(b'\n');assert raw==(w/p['raw_copy']).read_bytes();assert h(raw)==p['raw_line_sha256']
 row=json.loads(raw);assert str(row['mathdb_id'])==k;assert row['statement']==x['literal_statement'];assert h(row['statement'].encode())==p['statement_utf8_sha256'];assert x['accepted_credit']==0
 for s in x['sources_reviewed']:assert h((w/s['file']).read_bytes())==s['sha256']
inputs=[]
for path,expected in r['input_hashes'].items():
 p=pathlib.Path(path);actual=h(p.read_bytes());inputs.append({'path':path,'expected':expected,'actual':actual,'matches':expected==actual,'mutable_administrative_context':p.name=='ledger.json'})
assert all(x['matches'] or x['mutable_administrative_context'] for x in inputs)
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_id_count':len(d),'outcomes':dict(collections.Counter(x['outcome'] for x in d.values())),'raw_lines_verified':40,'manifest_bound_chunks_used':len(chunks),'new_primary_body_review_ids':[int(k) for k,v in d.items() if v['new_primary_body_review']],'accepted_credit':0,'reservation_input_checks':inputs,'lean_endpoint_count':0,'scope':'Raw bytes/newlines, one-based source positions, raw/chunk/statement/source hashes and exact reservation membership verified; no Lean proof/rebuild claimed.'}
(w/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
