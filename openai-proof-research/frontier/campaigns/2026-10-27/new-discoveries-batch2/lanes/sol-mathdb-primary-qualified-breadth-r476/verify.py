import pathlib,json,hashlib,sys,datetime,collections
D=pathlib.Path(__file__).resolve().parent;L=D.parent;W=pathlib.Path('/home/mj-kang/Documents/Dev/math')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(b,msg):
 if not b:raise AssertionError(msg)
def load(p):return json.loads(p.read_text())
def check(p,h,n=None):
 require(p.is_file(),f'missing {p}');require(sha(p)==h,f'hash mismatch {p}')
 if n is not None:require(p.stat().st_size==n,f'bytes mismatch {p}')
try:
 m=load(D/'manifest.json');excluded={'manifest.json','final-receipt.jsonl'}
 require(set(m['excluded_paths'])==excluded,'manifest exclusions')
 actual={str(p.relative_to(D)) for p in D.rglob('*') if p.is_file()}-excluded
 require(actual=={r['path'] for r in m['files']},'exact manifest payload')
 require(len(m['files'])==len(actual),'duplicate manifest paths')
 for r in m['files']:check(D/r['path'],r['sha256'],r['bytes'])
 for name in ['prefreeze.sha256','instructions-inputs.sha256']:
  for line in (D/name).read_text().splitlines():
   digest,path=line.split('  ',1);p=pathlib.Path(path);check(p if p.is_absolute() else W/p,digest)
 for r in load(D/'flat-bindings.json'):check(pathlib.Path(r['path']),r['sha256'],r['bytes'])
 # Independently re-read source manifests, without executing or importing source code.
 for lane in ['root-mathdb-breadth-intake-r475','root-mathdb-cayley-review-intake-r363','root-mathdb-accepted-exclusions-r304']:
  root=L/lane;u=load(root/'manifest.json');entries=u if isinstance(u,list) else u['files']
  for r in entries:check(root/r['path'],r['sha256'],r.get('bytes',r.get('size')))
  for r in load(root/'bindings.json'):
   for key in ['original','copy']:
    if key in r:
     p=pathlib.Path(r[key]);p=p if p.is_absolute() else root/p;check(p,r['sha256'],r.get('size',r.get('bytes')))
 V=L/'pi-mathdb-full-corpus-inventory-r301';im=load(V/'manifest.json')
 chunks=[x for x in im['files'] if x['path'].startswith('corpus/mathdb-normalized-chunk-')]
 require(len(chunks)==20 and len(im['frozen_inputs'])==8,'20/8 inventory groups')
 for r in chunks+im['frozen_inputs']:check(V/r['path'],r['sha256'],r['bytes'])
 I=L/'root-mathdb-breadth-intake-r475';res=load(I/'reserved-ids.json');ids=res['ids'];queue=load(I/'queue.json');cov=load(I/'coverage-delta.json')
 require(len(ids)==len(set(ids))==50 and ids==[r['mathdb_id'] for r in queue],'exact fifty queue')
 require(res['lane']==D.name,'owner assignment');require(len(cov)==3233,'baseline count')
 require(not set(ids)&{int(k) for k in cov},'prior coverage overlap')
 require(not set(ids)&set(res['other_active_reservations']),'active overlap')
 require(not set(ids)&{372627,372628,368940,404067,364119},'explicit exclusions')
 def associations(o):
  if isinstance(o,dict):
   for k,v in o.items():
    if ('id' in k or 'association' in k) and isinstance(v,int):yield v
    elif ('ids' in k or 'associations' in k) and isinstance(v,list):
     for t in v:
      if isinstance(t,int):yield t
      else:yield from associations(t)
    else:yield from associations(v)
  elif isinstance(o,list):
   for v in o:yield from associations(v)
 for name in ['accepted-exclusions.json','historical-dispositions.json']:
  require(not set(ids)&set(associations(load(L/'root-mathdb-accepted-exclusions-r304'/name))),'historical/accepted overlap')
 original={}
 for r in chunks:
  p=V/r['path']
  for n,b in enumerate(p.open('rb'),1):
   row=json.loads(b);i=row['mathdb_id']
   if i in ids:
    require(i not in original,'duplicate original ID');original[i]=(row,str(p),n,hashlib.sha256(b).hexdigest())
 require(set(original)==set(ids),'original exact fifty')
 dispositions=load(D/'dispositions.json');assigned=load(D/'assigned-records.json')
 require([r['mathdb_id'] for r in dispositions]==ids,'disposition ordered payload')
 require([r['record']['mathdb_id'] for r in assigned]==ids,'assigned ordered payload')
 for x in dispositions+assigned:
  r,p,n,bh=original[x['record']['mathdb_id']]
  require(x['record']==r,'original record payload')
  require(x['original_chunk']==p and x['original_line']==n and x['line_sha256']==bh,'original locator')
  require(x['statement_utf8_sha256']==hashlib.sha256(r['statement'].encode('utf-8')).hexdigest(),'literal UTF8 hash')
  require(x['canonical_record_sha256']==hashlib.sha256(json.dumps(r,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest(),'canonical record hash')
  if 'literal_statement' in x:
   require(x['literal_statement']==r['statement'],'literal statement exact')
   require(x['accepted_credit']==0 and not x['proposal'],'zero credit')
   for field in ['full_scope_mechanism_or_obstacle','formal_dependencies','strongest_objection','bounded_check','registry','prior_art_gaps']:require(bool(x[field]),field)
 require(load(D/'proposals.json')==[],'zero proposals')
 ledger=load(L.parent/'ledger.json');require((ledger['accepted_count'],ledger['total_accepted_count'],ledger['next_global_outcome_number'])==(9,39,40),'counts unchanged')
 for r in load(D/'sources.json'):
  if 'file' in r and 'sha256' in r:check(D/r['file'],r['sha256'],r.get('bytes'))
 check_result=load(D/'bounded-check.json');require(check_result['original_code']==[[],[1,2],[2,3],[3]] and [2] in check_result['source_proposed_perturbation_code'],'bounded certificate payload')
 print(json.dumps({'integrity':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(D/'manifest.json'),'payload_files':len(actual),'flat_bindings':len(load(D/'flat-bindings.json')),'exact_dispositions':50,'baseline_reported_reviews':3233,'chunks':20,'separately_listed_frozen_inputs':8,'proposals':0,'math_pass':False,'novelty_pass':False,'campaign_counts':[9,39,40]}))
except Exception as e:
 print(json.dumps({'integrity':'FAIL','error':repr(e)}));sys.exit(1)
