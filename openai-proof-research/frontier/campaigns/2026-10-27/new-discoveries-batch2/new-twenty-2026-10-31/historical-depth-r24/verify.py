import pathlib,json,hashlib,datetime,resource
resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,768*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(55,55))
D=pathlib.Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();J=lambda f:json.loads((D/f).read_bytes());r=J('reservation.json');out=J('results.json');raw=J('raw-bindings.json');old=J('old-dispositions.json');assert len(out)==40 and set(out)==set(map(str,r['ids']))
for p,h in r['prior_report_hashes'].items():assert H(pathlib.Path(p).read_bytes())==h,p
for id,x in raw.items():
 data=pathlib.Path(x['path']).read_bytes();assert H(data)==x['chunk_sha256'];line=data.splitlines(keepends=True)[x['line_one_based']-1];assert line==(D/'raw'/f'{id}.jsonl').read_bytes();assert H(line)==x['raw_line_sha256'];record=json.loads(line);assert record['mathdb_id']==int(id);assert record['statement']==old[id]['statement']==out[id]['literal_statement'];assert H(record['statement'].encode())==x['statement_sha256'];assert out[id]['old_disposition']==old[id];assert out[id]['accepted_credit']==out[id]['new_unique_record_review_credit']==0;assert out[id]['lean_endpoint'] is None
 if 'statement_sha256' in old[id]:assert old[id]['statement_sha256']==x['statement_sha256']
for x in J('input-verification.json')['chunks']:
 b=pathlib.Path(x['path']).read_bytes();assert len(b)==x['bytes'] and H(b)==x['sha256']
for filename in ['source-receipts.json','source-receipts-second.json']:
 for x in J(filename):
  if 'sha256' in x:assert H((D/'sources'/x['name']).read_bytes())==x['sha256']
assert H((D/'sources/halfsum').read_bytes())==J('source-receipt-halfsum.json')['sha256'];assert H((D/'sources/public-index').read_bytes())==J('public-index-receipt.json')['sha256'];assert H((D/'registry-head.json').read_bytes())==J('registry-receipt.json')['sha256']
rp=J('registry-reuse.json');assert H(pathlib.Path(rp['path']).read_bytes())==rp['sha256'];assert json.loads((D/'registry-head.json').read_bytes())['sha']==rp['head'];assert rp['truncated'] is False
manifest=J('manifest.json');expected={x['path'] for x in manifest['files']};actual={str(p.relative_to(D)) for p in D.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json','verify.log']};assert expected==actual
for x in manifest['files']:
 b=(D/x['path']).read_bytes();assert H(b)==x['sha256'] and len(b)==x['bytes'],x['path']
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',exact_results=40,immutable_prior_reports=3,corpus_chunks=20,exact_raw_lines=40,new_primary_contexts=sum(x['new_review']['primary_definitions'] for x in out.values()),selected_proof_contexts=sum(x['new_review']['selected_proof_bodies'] for x in out.values()),endpoints=0,accepted_credit=0,manifest_sha256=H((D/'manifest.json').read_bytes()),limits='Integrity check, not independent mathematical review or formal replay.')
(D/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
