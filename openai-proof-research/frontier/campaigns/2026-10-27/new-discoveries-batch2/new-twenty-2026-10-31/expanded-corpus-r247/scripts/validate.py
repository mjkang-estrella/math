import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1];rs=json.loads((L/'results.json').read_text());ids=json.loads((L/'reservation.json').read_text())['ids'];assert set(rs)==set(map(str,ids)) and len(rs)==20
for i,r in rs.items():
 b=(L/r['raw_line_file']).read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==r['provenance']['raw_sha256'];d=json.loads(b);assert d['mathdb_id']==int(i);assert d['statement']==r['literal_statement'];assert hashlib.sha256(r['literal_statement'].encode()).hexdigest()==r['statement_sha256'];assert r['credit']==0 and r['lean_endpoint'] is None
for name,r in json.loads((L/'http-manifest.json').read_text()).items():
 p=L/'http'/name;assert hashlib.sha256((p/'receipt.json').read_bytes()).hexdigest()==r['receipt_sha256']
 if r.get('sha256'):assert hashlib.sha256((p/'body').read_bytes()).hexdigest()==r['sha256']
assert not list(L.rglob('__pycache__'))
for name in ['SUMMARY.md','CANDIDATE.md']:assert (L/name).stat().st_size>0
s=json.loads((L/'sullivan6-results.json').read_text());assert s['complete'] and s['tested_labelled_orientations']==3**15 and s['fail_literal_disjunction']==0
r=json.loads((L/'randic16-results.json').read_text());assert r['rows'][-1]['n']==16 and r['rows'][-1]['tested']==19320 and all(x['complete'] for x in r['rows'])
v=json.loads((L/'laver9-results.json').read_text());assert v['printed_FM3_reproduced'] and v['rows'][-1]['n']==9 and not any(x['failure'] for x in v['rows'])
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','id_keyed_entries':20,'raw_statement_provenance':'PASS','http_receipt_and_body_hashes':'PASS','lane_bytecode_absent':True,'sullivan_max_order':6,'sullivan_order6_count':3**15,'tree_max_order':16,'tree_order16_count':19320,'laver_n_max':9,'laver_order':512,'laver_max_triples':v['rows'][-1]['triples_checked'],'new_solutions':0,'lean_endpoints':0,'qualification':'Validation of deliverable integrity and reported diagnostic coverage, not a proof or novelty certificate.'};(L/'validation.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
