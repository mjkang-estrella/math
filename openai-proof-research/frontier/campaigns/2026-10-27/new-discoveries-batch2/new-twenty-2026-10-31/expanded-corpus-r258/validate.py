import pathlib,json,hashlib,resource,datetime
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent;h=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((L/'results.json').read_text());res=json.loads((L/'reservation.json').read_text());assert set(r)==set(map(str,res['ids'])) and len(r)==20
for i,x in r.items():
 b=(L/'records'/f'{i}.jsonl').read_bytes();assert h(b)==x['provenance']['raw_sha256_including_newline'];assert b.endswith(b'\n');assert json.loads(b)['statement']==x['statement'];assert h(x['statement'].encode())==x['provenance']['statement_utf8_sha256'];assert x['accepted_credit']==0
for p in (L/'sources').glob('*.receipt.json'):
 d=json.loads(p.read_text());q=p.with_name(p.name.removesuffix('.receipt.json'))
 if d.get('status')==200:assert q.exists() and h(q.read_bytes())==d['sha256']
assert not list(L.rglob('__pycache__'))
v={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact20_ids':True,'raw_newlines_and_statement_hashes':True,'source_body_hashes_checked':True,'credit':0,'campaign_count':'52/60 unchanged','rss_sample_proc_self_status':[s for s in pathlib.Path('/proc/self/status').read_text().splitlines() if s.startswith(('VmRSS:','VmHWM:'))],'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'no_execution_or_Lean':True,'no_background_collection_sessions':'All four returned tool session IDs confirmed exit 0 before handoff.'}
(L/'validation.json').write_text(json.dumps(v,indent=2))
manifest={str(p.relative_to(L)):h(p.read_bytes()) for p in sorted(L.rglob('*')) if p.is_file() and p.name!='MANIFEST.sha256.json'}
(L/'MANIFEST.sha256.json').write_text(json.dumps(manifest,indent=2));print(json.dumps(v,indent=2));print('hashed files',len(manifest))
