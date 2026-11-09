"""Independent data verifier. No imported upstream code and no mutations."""
import pathlib,json,hashlib,re,datetime,sys
L=pathlib.Path(__file__).resolve().parent;B=L.parent;I=B/'root-mathdb-breadth-intake-r471';V=B/'pi-mathdb-full-corpus-inventory-r301'
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(pathlib.Path(p).read_bytes())
def ck(p,e):
 b=pathlib.Path(p).read_bytes();assert sha(b)==e['sha256'],str(p)
 if 'bytes' in e or 'size' in e:assert len(b)==e.get('size',e.get('bytes')),str(p)
 return b
def canonical(r):return sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
# Verify exact lane payload: no prefix exclusions, no unmanifested files.
m=read(L/'manifest.json');excluded={'manifest.json','final-receipt.txt'};assert set(m['excluded_exact_paths'])==excluded
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()};assert actual-excluded=={e['path'] for e in m['files']}
assert len(m['files'])==len({e['path'] for e in m['files']})
for e in m['files']:ck(L/e['path'],e)
# Freeze bindings are flat references. Independently rehash actual originals now.
refs=read(L/'bindings.json');assert len(refs)==len({e['path'] for e in refs})
for e in refs:ck(e['path'],e)
# Intake payload and original/copy pairs checked independently without executing its verifier.
im=read(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in im['files']}
for e in im['files']:ck(I/e['path'],e)
for e in read(I/'bindings.json'):ck(e['original'],e);ck(e['copy'],e)
for name in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=B/name;x=read(d/'manifest.json')
 for e in (x if isinstance(x,list) else x['files']):ck(d/e['path'],e)
vm=read(V/'manifest.json');chunks=[e for e in vm['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')];assert len(chunks)==20;assert len(vm['frozen_inputs'])==8
for e in chunks+vm['frozen_inputs']:ck(V/e['path'],e)
res=read(I/'reserved-ids.json');q=read(I/'queue.json');ids=res['ids'];wanted=set(ids);assert len(ids)==len(wanted)==50;assert wanted=={r['mathdb_id'] for r in q};assert res['lane']==L.name
coverage=read(I/'coverage-delta.json');assert len(coverage)==3133;assert not wanted&set(map(int,coverage));assert not wanted&set(res['other_active_reservations']);assert not wanted&{372627,372628,368940,404067,364119}
for f in ['accepted-exclusions.json','historical-dispositions.json']:
 txt=(B/'root-mathdb-accepted-exclusions-r304'/f).read_text();json.loads(txt)
 for i in ids:assert not re.search(r'(?<!\d)'+str(i)+r'(?!\d)',txt),(f,i)
D=read(L/'dispositions.json');R=read(L/'assigned-records.json');assert len(D)==50;assert wanted=={r['mathdb_id'] for r in D};assert len(R)==50
found={}
for e in chunks:
 p=V/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line);i=r.get('mathdb_id',r.get('id'))
  if i in wanted:assert i not in found;found[i]=(str(p),n,r)
assert set(found)==wanted
for d in D:
 p,n,r=found[d['mathdb_id']];assert (p,n)==(d['original_chunk'],d['original_line']);assert d['literal_statement']==r['statement'];assert sha(r['statement'].encode())==d['statement_utf8_sha256'];assert canonical(r)==d['canonical_record_sha256'];assert d['accepted_credit']==0;assert not d['prior_cleared'];assert not d['whole_primary_body_read'];assert not d['full_dependency_audit'];assert d['full_scope_mechanism_or_obstacle']
for a in R:
 p,n,r=found[a['record']['mathdb_id']];assert a['record']==r;assert a['chunk']==p and a['line']==n;assert a['canonical_record_sha256']==canonical(r)
for e in read(L/'retained-sources.json'):
 if 'path' in e:
  ck(L/e['path'],e);assert sha((L/'sources'/(e['arxiv_id']+'.txt')).read_bytes())==e['text_sha256'];assert e['url'].startswith('https://arxiv.org/pdf/');assert e['utc'];assert e['pdf_version_header']
assert read(L/'proposals.json')==[]
ledger=read(L.parent.parent/'ledger.json');assert (ledger['accepted_count'],ledger['total_accepted_count'],ledger['next_global_outcome_number'])==(9,39,40)
print(json.dumps({'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha((L/'manifest.json').read_bytes()),'payload_files':len(m['files']),'flat_bindings':len(refs),'chunks_checked_in_place':20,'separately_listed_frozen_inputs':8,'intake_original_bindings_checked':len(read(I/'bindings.json')),'baseline_reported_reviews':3133,'exact_statements_checked':50,'proposals':0,'math_novelty_status':'NOT PASS: HOLD / public-source exclusions; integrity PASS only','counts':[9,39,40]},indent=2))
