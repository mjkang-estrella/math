import pathlib,json,hashlib,resource,datetime
resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,768*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(30,30))
D=pathlib.Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();R=json.loads((D/'reservation.json').read_text());rows=json.loads((D/'results.json').read_text());assert len(rows)==40 and set(rows)==set(map(str,R['ids']))
for group in ['prior_report_hashes','input_hashes']:
 for p,h in R[group].items():assert H(pathlib.Path(p).read_bytes())==h
old={str(x['mathdb_id']):x for x in json.loads(pathlib.Path(next(iter(R['prior_report_hashes']))).read_text())}
chunks={}
for i,r in rows.items():
 assert r['old_disposition']==old[i] and r['prior_coverage']==R['prior_coverage'][i]
 p=pathlib.Path(r['raw_record']['path']);lines=chunks.setdefault(str(p),p.read_bytes().splitlines(keepends=True));raw=lines[r['raw_record']['one_based_line']-1];local=(D/r['raw_record']['local']).read_bytes();assert raw==local and H(raw)==r['raw_record']['sha256'];assert H(p.read_bytes())==r['raw_record']['chunk_sha256']
 x=json.loads(raw);assert str(x['mathdb_id'])==i and x['statement']==r['literal_statement']==old[i]['statement']
 assert H(x['statement'].encode())==old[i]['statement_sha256']==r['literal_statement_sha256']
 assert H(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())==old[i]['canonical_record_sha256']
 assert r['accepted_credit']==r['discovery_credit']==r['new_unique_record_coverage']==0
 assert not r['new_original_problem_body_review'] and not r['new_complete_dependency_audit'] and not r['source_scope_cleared']
for p in (D/'sources').glob('*.receipt.json'):
 r=json.loads(p.read_text());body=p.with_name(p.name.removesuffix('.receipt.json'))
 if r.get('status')==200:assert body.exists() and H(body.read_bytes())==r['sha256'] and len(body.read_bytes())==r['size']
for r in json.loads((D/'registry-reuse.json').read_text())['verified_refs']:assert H(pathlib.Path(r['path']).read_bytes())==r['sha256']
print(json.dumps(dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exact_ids=40,old_dispositions_preserved=40,literal_statement_and_canonical_hashes=40,raw_lines_preserved_with_newlines=40,immutable_reservation_inputs_verified=True,successful_source_receipts_verified=True,credit=0,new_unique_record_coverage=0,lean_endpoints=0),indent=2))
