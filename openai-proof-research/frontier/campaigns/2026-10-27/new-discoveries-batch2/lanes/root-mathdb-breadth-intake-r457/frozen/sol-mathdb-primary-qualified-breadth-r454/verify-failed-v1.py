"""Independent integrity verifier. Run only via mandated helper_guard.py; no upstream code."""
import pathlib,json,hashlib,datetime,sys
L=pathlib.Path(__file__).resolve().parent;B=L.parent;I=B/'root-mathdb-breadth-intake-r453';V=B/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_bytes())
def sha(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 assert p.is_file() and not p.is_symlink(),str(p)
 b=p.read_bytes();assert sha(b)==e['sha256'],('hash',str(p));assert len(b)==e.get('bytes',e.get('size')),('bytes',str(p))
def ids_in(x):
 out=set()
 if isinstance(x,dict):
  for k,v in x.items():
   if k in ('mathdb_id','record_id','problem_id') and isinstance(v,int):out.add(v)
   elif k in ('mathdb_ids','problem_ids') and isinstance(v,list):out.update(t for t in v if isinstance(t,int))
   else:out.update(ids_in(v))
 elif isinstance(x,list):
  for v in x:out.update(ids_in(v))
 return out
try:
 manifest=load(L/'manifest.json');files={p.relative_to(L).as_posix() for p in L.rglob('*') if p.is_file()};assert files==set(e['path'] for e in manifest['files'])|{'manifest.json','final-receipt.json'},('membership',files-set(e['path'] for e in manifest['files']))
 for e in manifest['files']:check(L/e['path'],e)
 bindings=load(L/'bindings.json');assert len({e['original'] for e in bindings})==len(bindings)
 assert load(L/'frozen_inputs.json')==[e['original'] for e in bindings]
 for e in bindings:check(pathlib.Path(e['original']),e)
 for e in load(I/'manifest.json')['files']:check(I/e['path'],e)
 for e in load(I/'bindings.json'):
  check(pathlib.Path(e['original']),e);check(pathlib.Path(e['copy']),e)
 chunks=[e for e in load(V/'manifest.json')['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
 for e in chunks:check(V/e['path'],e)
 for name in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
  m=load(B/name/'manifest.json')
  for e in (m['files'] if isinstance(m,dict) else m):check(B/name/e['path'],e)
 reserved=load(I/'reserved-ids.json');ids=reserved['ids'];S=set(ids);assert len(ids)==len(S)==50;assert reserved['lane']==L.name
 assert S=={r['mathdb_id'] for r in load(I/'queue.json')}
 assert not S&set(reserved['other_active_reservations'])
 coverage=load(I/'coverage-delta.json');assert len(coverage)==2733;assert not S&set(map(int,coverage))
 exclusions=ids_in(load(B/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json'))|ids_in(load(B/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json'))|{372627,372628,368940,404067,364119}
 assert not S&exclusions
 records=load(L/'assigned-records.json');D=load(L/'dispositions.json');assert len(D)==50 and {x['mathdb_id'] for x in D}==S
 assert len(records)==50 and {x['record']['mathdb_id'] for x in records}==S
 actual={};locations={}
 for e in chunks:
  p=V/e['path']
  for n,line in enumerate(p.open(encoding='utf-8'),1):
   r=json.loads(line);i=r.get('mathdb_id')
   if i in S:
    assert i not in actual;actual[i]=r;locations[i]=(str(p),n)
 for x in records:
  r=x['record'];i=r['mathdb_id'];assert r==actual[i];assert not r['historical'];assert r['statement_completeness']=='full'
  assert (x['original_chunk'],x['original_line'])==locations[i]
  canonical=sha(json.dumps(r,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode());assert x['canonical_record_sha256']==canonical
  d=next(d for d in D if d['mathdb_id']==i)
  assert d['literal_statement']==d['scope_and_quantifiers']==r['statement'];assert d['statement_utf8_sha256']==sha(r['statement'].encode());assert d['canonical_record_sha256']==canonical
  assert (d['original_chunk'],d['original_line'])==locations[i]
  assert d['credit']==0 and d['proof_level']=='NO_NEW_FULL_SCOPE_PROOF' and d['registry_level']=='HOLD_429_ZERO_MATHDB_REQUESTS'
  for k in ['full_scope_mechanism_or_obstacle','source_internal_check','source_level','closest_successor_check','bounded_check','strongest_objection','novelty_gaps']:assert d[k]
 assert load(L/'proposals.json')==[]
 sections=load(L/'primary-sections.json');assert len(sections)==50 and {x['id'] for x in sections}==S
 P=load(L/'source-provenance.json')
 for e in P:
  if 'path' in e:check(L/e['path'],e)
 for r in actual.values():
  name=r['source_url'].split('/')[-1]
  for suffix in ['html','pdf','txt']:assert any(e.get('path')=='sources/'+name+'.'+suffix for e in P)
  for suffix in ['html','pdf']:
   e=next(e for e in P if e.get('path')=='sources/'+name+'.'+suffix);assert e['utc'] and e['url'] and e['version']
 receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha((L/'manifest.json').read_bytes()),flat_originals=len(bindings),corpus_chunks=20,assigned=50,dispositions=50,prior_reported_reviews=2733,proposals=0,additional=9,total=39,next=40,mathematical_pass=False,novelty_pass=False,limitations='Integrity only; source passages not complete proof audits; successor and registry HOLD.')
 (L/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
except Exception as e:
 print('INTEGRITY FAIL:',repr(e),file=sys.stderr);sys.exit(1)
