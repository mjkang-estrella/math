import pathlib,json,hashlib,resource,os,datetime
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(30,30));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
o=pathlib.Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((o/'reservation.json').read_text());d=json.loads((o/'results.json').read_text());assert len(d)==40 and set(d)==set(map(str,r['ids']))
for p,h in r['prior_report_hashes'].items():assert sha(pathlib.Path(p).read_bytes())==h
cache={}
for i,x in d.items():
 assert not x['accepted_credit'] and not x['new_literal_record_review_count_credit'] and x['lean_endpoint'] is None
 ref=x['raw_reference'];p=pathlib.Path(ref['path'])
 if str(p) not in cache:
  data=p.read_bytes();assert sha(data)==ref['chunk_sha256'];cache[str(p)]=data.splitlines(keepends=True)
 line=cache[str(p)][ref['line']-1];assert sha(line)==ref['raw_sha256'] and line==(o/'raw'/f'{i}.jsonl').read_bytes();obj=json.loads(line);assert obj['mathdb_id']==int(i);assert obj['statement']==x['literal_statement'] and sha(obj['statement'].encode())==x['literal_statement_sha256']
assert sum(x['new_primary_body_review'] for x in d.values())==3
for x in json.loads((o/'source-receipts.json').read_text()):
 if 'path' in x:assert sha(pathlib.Path(x['path']).read_bytes())==x['sha256']
v=json.loads((o/'registry-reuse.json').read_text());assert sha(pathlib.Path(v['path']).read_bytes())==v['sha256'];head=json.loads((o/'sources/registry-head.json').read_text());assert head['sha']==v['head']
m=json.loads((o/'manifest.json').read_text());actual={str(p.relative_to(o)) for p in o.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json','verify.log']};assert actual==set(m)
for p,x in m.items():data=(o/p).read_bytes();assert sha(data)==x['sha256'] and len(data)==x['bytes']
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',exact_ids=40,new_primary_depth=3,new_record_review_credit=0,accepted_credit=0,prior_report_hashes_verified=4,raw_records_verified=40,payload_files=len(m),manifest_sha256=sha((o/'manifest.json').read_bytes()),limitations='Integrity only; not a Lean replay, mathematical acceptance or novelty clearance. Input ledger drift remains explicitly documented.')
(o/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
