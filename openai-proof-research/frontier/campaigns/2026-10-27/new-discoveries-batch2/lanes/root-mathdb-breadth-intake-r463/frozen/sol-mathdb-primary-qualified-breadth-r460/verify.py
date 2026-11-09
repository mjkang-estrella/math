"""Independent integrity verifier; executes no upstream code. Run only via required guard."""
import pathlib,json,hashlib,datetime,sys
L=pathlib.Path(__file__).resolve().parent;B=L.parent
J=lambda p:json.loads(p.read_text())
def H(b):return hashlib.sha256(b).hexdigest()
def check(p,h,n=None):
 p=pathlib.Path(p);b=p.read_bytes();assert H(b)==h,('hash',str(p));assert n is None or len(b)==n,('bytes',str(p))
def manifest(d):
 m=J(d/'manifest.json');files=m if isinstance(m,list) else m['files']
 for f in files:check(d/f['path'],f['sha256'],f.get('bytes',f.get('size')))
 return m
try:
 m=J(L/'manifest.json');expected={f['path'] for f in m['files']};actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-{'manifest.json','final-receipt.json'}
 assert expected==actual,('payload membership',expected^actual)
 for f in m['files']:check(L/f['path'],f['sha256'],f['bytes'])
 refs=J(L/'bindings.json');assert len({f['path'] for f in refs})==len(refs)
 for f in refs:check(f['path'],f['sha256'],f['bytes'])
 intake=B/'root-mathdb-breadth-intake-r459';manifest(intake)
 # Verify actual direct originals, never executing or expanding a bound verifier/bindings file.
 for name in ['root-mathdb-breadth-intake-r459','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
  d=B/name;manifest(d)
  for f in J(d/'bindings.json'):
   check(f['original'],f['sha256'],f.get('size',f.get('bytes')))
   cp=pathlib.Path(f.get('copy',f.get('frozen','')))
   if str(cp)!='.':check(cp if cp.is_absolute() else d/cp,f['sha256'],f.get('size',f.get('bytes')))
 inv=B/'pi-mathdb-full-corpus-inventory-r301';im=J(inv/'manifest.json');chunks=[f for f in im['files'] if f['path'].startswith('corpus/')]
 assert len(chunks)==20
 for f in chunks:check(inv/f['path'],f['sha256'],f['bytes'])
 frozen=im['frozen_inputs'];assert frozen==J(L/'inventory-frozen-membership.json')
 assert {f['path'] for f in frozen}=={str(p.relative_to(inv)) for p in (inv/'frozen').rglob('*') if p.is_file()}
 for f in frozen:check(inv/f['path'],f['sha256'],f['bytes'])
 a=J(intake/'reserved-ids.json');q=J(intake/'queue.json');ids=a['ids'];s=set(ids);coverage=J(intake/'coverage-delta.json')
 assert len(ids)==len(s)==50 and a['lane']==L.name
 assert s=={r['mathdb_id'] for r in q} and len(q)==50
 assert len(coverage)==2883 and not s&set(map(int,coverage))
 assert not s&set(a['other_active_reservations']) and not s&{372627,372628,368940,404067,364119}
 ex=set()
 def associations(o):
  if isinstance(o,dict):
   for k,v in o.items():
    if k in ('mathdb_id','problem_id','mathdb_related_id') and isinstance(v,int):ex.add(v)
    if k in ('mathdb_ids','problem_ids') and isinstance(v,list):ex.update(x for x in v if isinstance(x,int))
    associations(v)
  elif isinstance(o,list):
   for v in o:associations(v)
 for fn in ['accepted-exclusions.json','historical-dispositions.json']:associations(J(B/'root-mathdb-accepted-exclusions-r304'/fn))
 assert not s&ex
 rows=J(L/'records.json');dis=J(L/'dispositions.json');assert len(rows)==len(dis)==50 and {x['record']['mathdb_id'] for x in rows}==s and {x['mathdb_id'] for x in dis}==s
 assert J(L/'proposals.json')==[]
 index={x['mathdb_id']:x for x in dis};wanted=collections=None
 original={}
 for f in chunks:
  p=inv/f['path']
  for ln,b in enumerate(p.open('rb'),1):
   r=json.loads(b)
   if r['mathdb_id'] in s:
    assert r['mathdb_id'] not in original
    original[r['mathdb_id']]=(str(p),ln,b,r)
 assert set(original)==s
 for x in rows:
  r=x['record'];i=r['mathdb_id'];p,ln,b,orig=original[i];d=index[i]
  assert orig==r and p==x['original_chunk'] and ln==x['original_line']
  assert H(b)==x['line_sha256']==d['original_line_sha256']
  assert H(r['statement'].encode('utf-8'))==x['statement_sha256']==d['statement_sha256_utf8']
  assert H(json.dumps(r,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode())==x['canonical_record_sha256']==d['canonical_record_sha256']
  assert d['literal_statement']==r['statement'] and d['literal_statement_read'] is True and d['proposed_credit']==0
  assert d['original_chunk']==p and d['original_line']==ln
  assert all(d[k] for k in ['full_scope_mechanism_or_obstacle','source_level','proof_level','registry_level','bounded_check','strongest_objection'])
  qr=next(z for z in q if z['mathdb_id']==i)
  for k in ['title','canonical_url','statement_completeness','post_type']:assert qr[k]==r[k],(i,k)
 for src in J(L/'sources.json'):
  check(src['pdf'],src['pdf_sha256'],src['bytes']);check(src['text'],src['text_sha256'])
 counts={k:sum(x['disposition']==k for x in dis) for k in {x['disposition'] for x in dis}}
 assert counts=={'HOLD':46,'EXCLUDE_PRIOR_SOURCE':3,'HOLD_PRIOR_REPORT':1}
 receipt={'integrity':'PASS','mathematical_novelty':'NOT_PASSED','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':H((L/'manifest.json').read_bytes()),'verify_sha256':H(pathlib.Path(__file__).read_bytes()),'payload_files':len(expected),'flat_input_bindings':len(refs),'chunks_checked_in_place':20,'statements':50,'dispositions':counts,'proposals':0,'baseline_reported_statement_reviews':2883,'counts_unchanged':{'additional':9,'total':39,'next':40},'procedural_caveat':'Campaign AGENTS.md read late; disclosed in failures and SUMMARY. Integrity PASS is not a procedure or source/dependency/novelty PASS.'}
 assert not (L/'final-receipt.json').exists(),'Refuse to alter an existing receipt'
 (L/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
except Exception as e:
 print('INTEGRITY FAIL:',repr(e),file=sys.stderr);sys.exit(1)
