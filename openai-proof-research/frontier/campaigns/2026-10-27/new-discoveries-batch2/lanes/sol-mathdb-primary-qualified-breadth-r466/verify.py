"""Independent read-only integrity verifier. Never imports upstream code."""
import pathlib,json,hashlib,sys
L=pathlib.Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(pathlib.Path(p).read_text())
def check(p,e):
 b=pathlib.Path(p).read_bytes(); assert H(b)==e['sha256'],str(p)
 for key in ['size','bytes']:
  if key in e:assert len(b)==e[key],str(p)
def ids(x):
 s=set()
 if isinstance(x,dict):
  for k,v in x.items():
   if k in ('mathdb_id','related_mathdb_id') and isinstance(v,int):s.add(v)
   elif k in ('mathdb_ids','problem_ids') and isinstance(v,list):s.update(v)
   else:s|=ids(v)
 elif isinstance(x,list):
  for y in x:s|=ids(y)
 return s
try:
 m=J(L/'manifest.json'); excluded={'manifest.json','final-receipt.txt'}; assert set(m['excluded'])==excluded and len(m['excluded'])==2
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-excluded
 named=[e['path'] for e in m['files']]; assert len(set(named))==len(named) and set(named)==actual
 for e in m['files']:check(L/e['path'],e)
 b=J(L/'bindings.json'); refs=b['flat_refs']; assert len({e['path'] for e in refs})==len(refs)
 for e in refs:check(e['path'],e)
 for name in ['root-mathdb-breadth-intake-r465','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
  d=L.parent/name; x=J(d/'manifest.json'); entries=x if isinstance(x,list) else x['files']
  for e in entries:check(d/e['path'],e)
  for e in J(d/'bindings.json'):
   check(e['original'],e)
   cp=pathlib.Path(e['copy']); check(cp if cp.is_absolute() else d/cp,e)
 V=L.parent/'pi-mathdb-full-corpus-inventory-r301'; inv=J(V/'manifest.json'); chunks=[e for e in inv['files'] if e['path'].startswith('corpus/')]; assert len(chunks)==20
 assert set(b['frozen_inputs'])=={str(V/e['path']) for e in chunks}
 fi=J(L/'inventory-frozen-inputs.json'); assert {e['path'] for e in fi}=={str(V/e['path']) for e in inv['frozen_inputs']}
 for e in inv['frozen_inputs']:check(V/e['path'],e)
 for e in fi:check(e['path'],e)
 I=L.parent/'root-mathdb-breadth-intake-r465'; r=J(I/'reserved-ids.json'); q=J(I/'queue.json'); cov=J(I/'coverage-delta.json'); assert len(cov)==3033
 assigned=set(r['ids']); assert len(r['ids'])==len(assigned)==50 and assigned=={e['mathdb_id'] for e in q} and len(q)==50 and r['lane']==L.name
 ex=set(map(int,cov))|set(r['other_active_reservations'])|{372627,372628,368940,404067,364119}
 for p in [L.parent/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L.parent/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L.parent/'root-mathdb-cayley-review-intake-r363/disposition.json']:ex|=ids(J(p))
 assert not assigned&ex
 orig={}
 for e in chunks:
  p=V/e['path'];check(p,e)
  for n,line in enumerate(p.open(),1):
   x=json.loads(line); ident=x['mathdb_id']
   if ident in assigned:
    assert ident not in orig;orig[ident]=(x,str(p),n)
 assert set(orig)==assigned
 ds=J(L/'dispositions.json'); ars=J(L/'assigned-records.json'); assert len(ds)==50 and {d['mathdb_id'] for d in ds}==assigned and len(ars)==50
 for a in ars:
  x,p,n=orig[a['record']['mathdb_id']];assert a['record']==x and str(V/a['chunk'])==p and a['line']==n
 for d in ds:
  x,p,n=orig[d['mathdb_id']];assert d['literal_statement']==x['statement'] and d['statement_utf8_sha256']==H(x['statement'].encode())
  assert d['canonical_record_sha256']==H(json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()) and d['original_chunk']==p and d['original_line_1based']==n
  assert d['accepted_credit']==0 and d['full_scope_mechanism_or_obstacle'] and d['registry_level'].startswith('HOLD')
 assert J(L/'proposals.json')==[]
 for e in J(L/'retained-sources.json'):
  if 'file' in e:check(L/e['file'],e);assert H((L/e['text_file']).read_bytes())==e['text_sha256']
 print(json.dumps({'integrity':'PASS','scientific_acceptance':'NOT_CLEARED','novelty':'HOLD','exact_dispositions':50,'baseline_reported_statement_reviews':3033,'verified_corpus_chunks':20,'inventory_frozen_inputs':len(fi),'proposals':0,'credit':0,'counts':'9 additional /39 total /next40','payload_files':len(named),'flat_refs':len(refs)},sort_keys=True))
except Exception as e:
 print(json.dumps({'integrity':'FAIL','error':str(e),'type':type(e).__name__}));sys.exit(1)
