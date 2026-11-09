import pathlib,json,hashlib,resource,os,datetime
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
L=pathlib.Path(__file__).resolve().parent;H=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
r=json.loads((L/'reservation.json').read_text());d=json.loads((L/'results.json').read_text());assert set(d)==set(map(str,r['ids'])) and len(d)==40
for p,h in r['prior_report_hashes'].items():assert H(p)==h
for x in d.values():
 ref=x['raw_binding'];p=pathlib.Path(ref['path']);assert H(p)==ref['chunk_sha256'];raw=p.read_bytes().splitlines(keepends=True)[ref['line_one_based']-1];assert raw==(L/'raw'/f"{x['mathdb_id']}.jsonl").read_bytes();assert hashlib.sha256(raw).hexdigest()==ref['raw_line_with_newline_sha256'];assert hashlib.sha256(x['literal_statement'].encode()).hexdigest()==x['old_disposition_verbatim']['statement_sha256'];assert x['accepted_credit']==0 and x['new_unique_coverage_credit']==0
for rec in json.loads((L/'source-receipts.json').read_text())+json.loads((L/'additional-receipts.json').read_text()):
 assert rec['status']==200 and H(L/rec['file'])==rec['sha256']
 if 'text_sha256' in rec:assert H((L/rec['file']).with_suffix('.txt'))==rec['text_sha256']
g=json.loads((L/'registry-review.json').read_text());assert H(g['reuse']['path'])==g['reuse']['sha256'] and H(g['reuse']['receipt_path'])==g['reuse']['receipt_sha256']
for x in json.loads((L/'context-bindings.json').read_text())['refs']:
 if not x['mutable_administrative']:assert H(x['path'])==x['sha256']
for p,h in json.loads((L/'manifest.json').read_text())['files'].items():assert H(L/p)==h,p
assert sum(x['new_primary_body_review'] for x in d.values())==2
print(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','id_rows':40,'new_related_primary_body_rows':2,'new_original_workshop_body_rows':0,'new_unique_coverage':0,'credit':0,'lean_endpoint':None,'scope':'Bindings and payload verification only; not mathematical proof verification.'},indent=2))
