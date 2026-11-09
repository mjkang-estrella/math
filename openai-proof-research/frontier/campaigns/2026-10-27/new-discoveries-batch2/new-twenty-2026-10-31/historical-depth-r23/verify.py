import pathlib,json,hashlib,resource,os,datetime
resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(60,)*2);os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
o=pathlib.Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((o/'reservation.json').read_text());results=json.loads((o/'results.json').read_text());raw=json.loads((o/'raw-record-bindings.json').read_text())
assert len(results)==40 and set(results)==set(map(str,r['ids']))
for path,want in {**r['prior_report_hashes'],**r['input_hashes']}.items():assert H(pathlib.Path(path))==want,path
for x in json.loads((o/'chunk-verification.json').read_text()):assert H(pathlib.Path(x['path']))==x['sha256']
for sid,x in results.items():
 b=raw[sid];p=pathlib.Path(b['path']);line=p.read_bytes().splitlines(keepends=True)[b['line_1based']-1];assert line==(o/'raw'/f'{sid}.jsonl').read_bytes();assert hashlib.sha256(line).hexdigest()==b['raw_line_sha256'];record=json.loads(line);assert str(record.get('id',record.get('mathdb_id')))==sid;assert record['statement']==b['literal_statement'];assert x['raw']==b;assert x['accepted_credit']==0 and x['lean_endpoint'] is None and x['unique_record_coverage_credit']==0;assert x['inherited']['reservation_coverage']==r['prior_coverage'][sid]
for name in ['source-receipts.json','successor-receipts.json','formal-registry-receipts.json']:
 for rec in json.loads((o/name).read_text()):
  assert rec['status']==200 and 'error' not in rec
  ps=list((o/'sources').glob(rec['name']+'.pdf'))+list((o/'sources').glob(rec['name']+'.json'));assert len(ps)==1;assert H(ps[0])==rec['sha256']
s=json.loads((o/'registry-screen.json').read_text());assert H(pathlib.Path(s['preprints_tree_path']))==s['preprints_tree_sha256'];assert not s['truncated'];assert s['head']==json.loads((o/'sources/registry.json').read_text())['sha']
env=json.loads((o/'environment.json').read_text());assert H(pathlib.Path(env['lean_path']))==env['lean_binary_sha256'];assert H(pathlib.Path(env['lake_manifest_path']))==env['lake_manifest_sha256'];assert not env['formal_work_performed']
assert sum(x['new_primary_body_review'] for x in results.values())==4;assert sum(x['new_successor_body_review'] for x in results.values())==2;assert sum(x['new_full_target_concluding_proof_read'] for x in results.values())==1
manifest=json.loads((o/'manifest.json').read_text());files={str(p.relative_to(o)) for p in o.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json','verification.log']};assert files==set(manifest)
for name,h in manifest.items():assert H(o/name)==h,name
rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','records':40,'raw_lines_verified':40,'chunks_verified':20,'immutable_prior_reports_verified':5,'new_primary_selections':4,'new_successor_selections':2,'full_target_public_closing_proof_selections':1,'complete_dependency_audits':0,'lean_endpoints':0,'proposed_credit':0,'scope':'Integrity and reporting consistency only; not mathematical acceptance or proof audit.'};(o/'verification-receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
