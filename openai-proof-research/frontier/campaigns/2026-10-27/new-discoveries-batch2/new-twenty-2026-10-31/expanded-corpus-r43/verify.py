import pathlib,json,hashlib,resource,datetime
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(20,20))
w=pathlib.Path(__file__).resolve().parent;r=json.loads((w/'reservation.json').read_text());d=json.loads((w/'results.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
assert len(d)==40 and set(d)==set(map(str,r['ids']))
for i,x in d.items():
 b=(w/x['raw_file']).read_bytes();assert b.endswith(b'\n') and sha(b)==x['raw_sha256'];y=json.loads(b);assert y['mathdb_id']==int(i);assert sha(y['statement'].encode())==x['statement_sha256'];assert y['statement']==x['literal_statement'];assert x['accepted_credit']==0 and not x['Lean_complete']
for x in json.loads((w/'source-receipts.json').read_text()):
 if x.get('status')==200:assert sha(pathlib.Path(x['file']).read_bytes())==x['sha256']
assert not list(w.rglob('*.lean'))
ledger=json.loads((w.parent/'ledger.json').read_text());assert ledger['accepted_new']==3
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact40':True,'raw_newlines_hashes_literals':True,'successful_HTTP_bodies_hashes':True,'no_Lean_endpoint':True,'accepted_credit_sum':0,'campaign_accepted_new':3,'counts_unchanged_by_worker':True,'limitation':'Artifact/provenance checks only, not mathematical or novelty certification.'}
(w/'verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
manifest={str(p.relative_to(w)):{'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size} for p in sorted(w.rglob('*')) if p.is_file() and p.name not in ['artifact-manifest.json','verification.log']}
(w/'artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
