import pathlib,json,hashlib,datetime,sys,resource,os
L=pathlib.Path(__file__).resolve().parent;B=L.parent
H=lambda b:hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def check(p,h,n=None):
 p=pathlib.Path(p);b=p.read_bytes();assert H(b)==h,('hash',str(p));assert n is None or len(b)==n,('bytes',str(p))
def ids_in(o):
 out=set()
 if isinstance(o,dict):
  for k,v in o.items():
   if k in ('mathdb_id','mathdb_ids','problem_ids'):
    for z in (v if isinstance(v,list) else [v]):
     if isinstance(z,int):out.add(z)
   out |= ids_in(v)
 elif isinstance(o,list):
  for v in o:out |= ids_in(v)
 return out
assert resource.getrlimit(resource.RLIMIT_AS)[0]==512*1024*1024
assert resource.getrlimit(resource.RLIMIT_CPU)[0]<=210
assert all(os.environ.get(k)=='1' for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','PYTHONDONTWRITEBYTECODE'])
# First recheck flat frozen references; never execute or recursively follow upstream code/bindings.
refs=load(L/'bindings.json');assert len({r['path'] for r in refs})==len(refs)
for r in refs:check(r['path'],r['sha256'],r['bytes'])
for name in ['root-mathdb-breadth-intake-r449','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=B/name;m=load(d/'manifest.json')
 for f in (m['files'] if isinstance(m,dict) else m):check(d/f['path'],f['sha256'],f.get('bytes',f.get('size')))
 for r in load(d/'bindings.json'):
  p=pathlib.Path(r['copy']);p=p if p.is_absolute() else d/p
  check(p,r['sha256'],r.get('size'));check(r['original'],r['sha256'],r.get('size'))
I=B/'pi-mathdb-full-corpus-inventory-r301';m=load(I/'manifest.json')
chunks=[x for x in m['files'] if x['path'].startswith('corpus/') and x['path'].endswith('.jsonl')];assert len(chunks)==20
assert {x['path'] for x in chunks}=={str(p.relative_to(I)) for p in (I/'corpus').glob('*.jsonl')}
for f in chunks:check(I/f['path'],f['sha256'],f['bytes'])
for f in m.get('frozen_inputs',[]):check(I/f['path'],f['sha256'],f.get('bytes',f.get('size')))
T=B/'root-mathdb-breadth-intake-r449';r=load(T/'reserved-ids.json');assigned=r['ids'];other=r['other_active_reservations'];q=load(T/'queue.json');cov=load(T/'coverage-delta.json')
assert len(assigned)==len(set(assigned))==50;assert len(other)==len(set(other))==50;assert len(cov)==2633
assert set(assigned)=={a['mathdb_id'] for a in q};assert len(q)==50
excluded=ids_in(load(B/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json'))|ids_in(load(B/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json'))|{372627,372628,368940,404067,364119}
assert not set(assigned)&(set(other)|set(map(int,cov))|excluded)
found={}
for f in chunks:
 p=I/f['path']
 with p.open() as stream:
  for n,line in enumerate(stream,1):
   a=json.loads(line);i=a['mathdb_id']
   if i in assigned:
    assert i not in found;found[i]=(a,str(p),n)
assert set(found)==set(assigned)
ds=load(L/'dispositions.json');ars=load(L/'assigned-records.json');assert len(ds)==50;assert len(ars)==50;assert {a['mathdb_id'] for a in ds}==set(assigned)
for d in ds:
 a,p,n=found[d['mathdb_id']];assert d['statement']==a['statement'];assert H(a['statement'].encode('utf-8'))==d['statement_utf8_sha256']
 assert H(json.dumps(a,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode())==d['canonical_record_sha256']
 assert (p,n)==(d['original_chunk'],d['original_line']);assert d['accepted_credit']==0
 assert d['technical_disposition'] and d['source_evidence_level'] and d['bounded_check']
for x in ars:
 a,p,n=found[x['record']['mathdb_id']];assert a==x['record'];assert (p,n)==(x['original_chunk'],x['original_line'])
assert load(L/'proposals.json')==[]
payload=load(L/'manifest.json');assert payload['excluded']==['manifest.json','final-receipt.json']
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(payload['excluded'])
listed={f['path'] for f in payload['files']};assert len(listed)==len(payload['files']);assert actual==listed,('payload membership',actual^listed)
for f in payload['files']:check(L/f['path'],f['sha256'],f['bytes'])
for f in load(L/'source-provenance.json')['files']:check(L/f['file'],f['sha256'],f['bytes'])
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_sha256':H((L/'manifest.json').read_bytes()),'verifier_sha256':H(pathlib.Path(__file__).read_bytes()),'payload_files':len(listed),'flat_references_rechecked':len(refs),'original_bindings_rechecked':True,'corpus_chunks_rechecked_in_place':20,'assignments':50,'other_active_reservations_excluded':50,'baseline_reported_reviews':2633,'dispositions':50,'proposals':0,'accepted_credit':0,'campaign_counts':'9 additional / 39 total / next 40','resource_caps':'512 MiB / CPU 210s / wall guard 230s','meaning':'Integrity only. No mathematical proof or novelty certification.'}
if '--receipt' in sys.argv:(L/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
