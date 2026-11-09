import pathlib,json,hashlib,sys,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;F=P/'frozen';I=F/'root-mathdb-breadth-intake-r653';C=L/'pi-mathdb-full-corpus-inventory-r301'
SPEC=[('sol-mathdb-primary-qualified-breadth-r652',5033,'455fa6b8f2d8f22555129f2637e298e231418efd14b778cd0b59f2b24118ca33','root-mathdb-breadth-intake-r651/reserved-ids-r652.json','corpus_chunk','corpus_line','statement_utf8_sha256')]
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),str(p);assert h(b)==e['sha256'],str(p)
def write(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
def exact(root,m):
 names={e['path'] for e in m['files']};assert len(names)==len(m['files'])
 assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==names
 for e in m['files']:check(root/e['path'],e)
def validate():
 for e in j(P/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 exact(L/'root-mathdb-breadth-intake-r653',j(I/'manifest.json'))
 for e in j(L/'root-mathdb-breadth-intake-r653/bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 cm=j(F/'pi-mathdb-full-corpus-inventory-r301/manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==7233
 data={};allids=set()
 for name,size,sha,res,ck,lk,hk in SPEC:
  check(F/name/'manifest.json',{'size':size,'sha256':sha});m=j(F/name/'manifest.json');exact(F/name,m);exact(L/name,m)
  for e in j(F/name/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
  ds=j(F/name/'dispositions.json');ids={d['mathdb_id'] for d in ds};assert len(ds)==len(ids)==50 and ids==set(j(F/res)['ids']);assert not ids&allids and not set(map(str,ids))&set(cov);allids|=ids;data[name]=ds
  assert j(F/name/'proposals.json')==[]
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in allids:assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(p,n,r)
 assert len(found)==50
 for name,_,_,_,ck,lk,hk in SPEC:
  for d in data[name]:
   p,n,r=found[d['mathdb_id']];assert d[ck]==str(p) and d[lk]==n and d['literal_statement_utf8']==r['statement'];assert d[hk]==h(r['statement'].encode());assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert d['accepted_credit']==0
 return cov,data
def build():
 cov,data=validate()
 for name,_,_,_,_,_,hk in SPEC:
  for d in data[name]:cov[str(d['mathdb_id'])]={'source_lane':name,'reported_disposition':d['disposition'],'statement_utf8_sha256':d[hk],'canonical_record_sha256':d['canonical_record_sha256'],'accepted_credit':0,'current_registry_cleared':False,'root_reconciled':True,'evidence_limit':'Reported literal review; selected source readings and finite checks not upgraded to complete proof/novelty audits'}
 for name,ds in data.items():
  for d in ds:
   if 'complete_self_contained_statement' in d:cov[str(d['mathdb_id'])]['reported_complete_self_contained_statement']=d['complete_self_contained_statement']
 for ds in data.values():
  for d in ds:
   for k in ['self_contained','scope_flags','statement_scope','evidence_level','independent_statement_flag','source_coverage','literal_statement_scope','complete_mathematical_statement_review','technical_statement_class','source_scope_flags','source_body_coverage','complete_statement','incomplete_record','missing_definitions','ambiguous_scope','scope_flag','complete_mathematical_statement_coverage','evidence','technical_statement_scope','complete','incomplete','definition_dependent','scope_ambiguous','independent_scope_classification','source_evidence','reviewed_scope','flags','technical_scope','definition_and_mechanism_assessment','scope_category','scope_category_basis','classification','classification_reason_and_quantifiers','classification_reason','quantifier_scope','completeness_classification','completeness_reason','statement_completeness']:
    if k in d:cov[str(d['mathdb_id'])]['reported_'+k]=d[k]
 for ds in data.values():
  for d in ds:
   if d.get('statement_completeness')=='incomplete' or d.get('completeness_classification')=='incomplete' or d.get('classification')=='incomplete' or d.get('scope_category')=='incomplete' or d.get('flags',{}).get('incomplete') is True or str(d.get('reviewed_scope','')).startswith('incomplete') or d.get('independent_scope_classification')=='incomplete' or d.get('incomplete') is True or d.get('scope_flag')=='incomplete' or d.get('incomplete_record') is True or d.get('independent_statement_flag')=='incomplete' or d.get('literal_statement_scope')=='incomplete' or d.get('technical_statement_class')=='incomplete':cov[str(d['mathdb_id'])].update({'complete_mathematical_statement_reviewed':False,'source_restoration_required':True})
 for ds in data.values():
  for d in ds:cov[str(d['mathdb_id'])]['reported_complete_mathematical_statement_reviewed']=d['statement_completeness']=='complete'
 write('coverage-delta.json',cov)
 for n in ['adjudications.json','hypothesis-queue.json','focused-assignment.json']:write(n,j(I/n))
 active=[r for r in j(I/'active-breadth-reservations.json') if r['lane'] not in {x[0] for x in SPEC}]
 blocked=set(map(int,cov))|{i for r in active for i in r['ids']}|set(active[0]['protected_ids'])
 route=[json.loads(l) for l in (I/'routing-queue.jsonl').open()];assert len(route)==8000
 (P/'routing-queue.jsonl').write_bytes((I/'routing-queue.jsonl').read_bytes())
 rows=[r for r in route if r['mathdb_id'] not in blocked][:50];assert len(rows)==50
 for n,part in [(656,rows)]:
  res={'lane':f'sol-mathdb-primary-qualified-breadth-r{n}','ids':[r['mathdb_id'] for r in part],'coverage_baseline':7283,'protected_ids':active[0]['protected_ids'],'active_hypothesis_ids':[],'status':'reserved_not_reviewed'}
  active.append(res);write(f'queue-r{n}.json',part);write(f'reserved-ids-r{n}.json',res)
 allids={i for r in active for i in r['ids']};assert len(allids)==150
 for r in active:r['other_active_reservations']=sorted(allids-set(r['ids']))
 
 for r in active:
  if r['lane']=='claude-mathdb-primary-qualified-breadth-r628':r['status']='rate_limit_held_not_reconciled'
 write('active-breadth-reservations.json',active)
 (P/'DECISION.md').write_text('# Root r655 reconciliation\n\nReconciled Sol r652: fifty disjoint literal record reviews; zero proposals/credit. Cumulative7,283 record reviews. Reported classifications13 complete,23 definition-dependent,10 scope-ambiguous,4 incomplete retained. Incomplete rows require restoration; completeness of formulation is not proof or novelty clearance.\n\nWorker reports eight selected primary passages,two selected successor passages,one whole Tadmor contribution and two local proof passages. Scalar resolvent negation and other source-known results earn no credit. Additive-cube and knot-invariant successor theorem endpoints were read; computational/dependency chains not replayed. Bounded checks are not general proof clearance. Current registry remains HOLD. Late derivative binding and truncated context output remain disclosed; final integrity does not erase timing deviations. Root verifies actual bytes,corpus identity and assignments only,no mathematical replay.\n\nCounts9additional/39total/next40 unchanged. Sol r654 continues; fresh Sol r656 gets queue-r656.json/reserved-ids-r656.json. Claude r628 rate-limit reservation remains held untouched. Three disjoint reserved sets; no focused hypothesis. Adjudications and access/privacy stops unchanged. Routing8,000metadata rows uncredited. No user input required.\n')
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and str(p.relative_to(P)) not in {'manifest.json','verification-receipt.json'}:
   b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'sha256':h(b),'size':len(b)})
 write('manifest.json',{'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':files})
def verify():
 old,data=validate();cov=j(P/'coverage-delta.json');assert len(cov)==7283 and set(cov)==set(old)|{str(d['mathdb_id']) for ds in data.values() for d in ds}
 for k,v in old.items():assert cov[k]==v
 assert cov['344924']['complete_mathematical_statement_reviewed'] is False and cov['344924']['source_restoration_required'] is True
 active=j(P/'active-breadth-reservations.json');seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not set(map(str,ids))&set(cov) and not ids&set(r['protected_ids']);seen|=ids
 assert len(seen)==150
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 for n in [656]:assert set(j(P/f'reserved-ids-r{n}.json')['ids'])=={r['mathdb_id'] for r in j(P/f'queue-r{n}.json')}
 assert (P/'routing-queue.jsonl').read_bytes()==(I/'routing-queue.jsonl').read_bytes()
 exact(P,j(P/'manifest.json'))
 try:check(P/'DECISION.md',{'size':0,'sha256':'0'*64})
 except AssertionError:pass
 else:raise AssertionError('negative accepted')
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','coverage':7283,'new_literal_record_reviews':50,'explicit_source_restoration_ids':sorted(int(k) for k,r in cov.items() if r.get('source_restoration_required')),'root_binding_pairs':len(j(P/'bindings.json')),'child_payloads':{name:len(j(F/name/'manifest.json')['files']) for name in data},'original_chunks':20,'frozen_inputs':8,'reservation_disjointness':True,'negative_rejection':True,'scientific_acceptance':False,'counts':{'additional':9,'total':39,'next':40}};write('verification-receipt.json',r);print(json.dumps(r))
if '--build' in sys.argv:build();print('built')
else:verify()
