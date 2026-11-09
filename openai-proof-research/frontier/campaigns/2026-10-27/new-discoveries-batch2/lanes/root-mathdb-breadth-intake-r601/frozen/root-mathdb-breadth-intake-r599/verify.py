import pathlib,json,hashlib,sys,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;F=P/'frozen';I=F/'root-mathdb-breadth-intake-r597';C=L/'pi-mathdb-full-corpus-inventory-r301'
SPEC=[('sol-mathdb-primary-qualified-breadth-r596',4296,'d2d6be5567fa5cbd78b4a85b412736cca7f6eb247106508fb333993ab41614df','root-mathdb-breadth-intake-r595/reserved-ids.json','corpus_path','corpus_line_1based','statement_utf8_sha256')]
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),str(p);assert h(b)==e['sha256'],str(p)
def write(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
def exact(root,m):
 names={e['path'] for e in m['files']};assert len(names)==len(m['files'])
 assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==names
 for e in m['files']:check(root/e['path'],e)
def routing_pool():
 old=[json.loads(l) for l in (I/'routing-queue.jsonl').open()];oldids={r['mathdb_id'] for r in old};assert len(old)==len(oldids)==6000
 ref=next(e for e in j(P/'bindings.json') if e['original'].endswith('screening-tags.jsonl'));p=pathlib.Path(ref['original']);check(p,ref)
 cm=j(F/'pi-mathdb-full-corpus-inventory-r301/manifest.json');expected=next(e for e in cm['files'] if e['path']=='tags/screening-tags.jsonl');check(p,expected)
 extra=[]
 for line in p.open():
  r=json.loads(line)
  if r['mathdb_id'] not in oldids and r.get('status')=='open' and r.get('statement_completeness')=='full':extra.append({k:r[k] for k in old[0] if k in r})
 extra.sort(key=lambda r:(-r['review_priority_score'],r['mathdb_id']));assert len(extra)>=2000
 out=old+extra[:2000];assert len({r['mathdb_id'] for r in out})==8000
 return out
def validate():
 for e in j(P/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 exact(L/'root-mathdb-breadth-intake-r597',j(I/'manifest.json'))
 cm=j(F/'pi-mathdb-full-corpus-inventory-r301/manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==5883
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
   p,n,r=found[d['mathdb_id']];assert d[ck]==str(p) and d[lk]==n and d['statement']==r['statement'];assert d[hk]==h(r['statement'].encode());assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert d['accepted_credit']==0
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
   for k in ['self_contained','scope_flags','statement_scope']:
    if k in d:cov[str(d['mathdb_id'])]['reported_'+k]=d[k]
 write('coverage-delta.json',cov)
 for n in ['adjudications.json','hypothesis-queue.json']:write(n,j(I/n))
 active=[r for r in j(I/'active-breadth-reservations.json') if r['lane']!='sol-mathdb-primary-qualified-breadth-r596']
 blocked=set(map(int,cov))|{i for r in active for i in r['ids']}|set(active[0]['protected_ids'])
 route=routing_pool()
 (P/'routing-queue.jsonl').write_bytes((I/'routing-queue.jsonl').read_bytes()+''.join(json.dumps(r,ensure_ascii=False,sort_keys=True)+'\n' for r in route[6000:]).encode())
 write('routing-expansion.json',{'prior_rows':6000,'added_rows':2000,'total_rows':8000,'new_technical_reviews':0,'criterion':'Remaining open/full inventory-tag records sorted descending review_priority_score then ascending mathdb_id; metadata routing only, no completeness endorsement'})
 rows=[r for r in route if r['mathdb_id'] not in blocked][:50];assert len(rows)==50
 res={'lane':'sol-mathdb-primary-qualified-breadth-r600','ids':[r['mathdb_id'] for r in rows],'coverage_baseline':5933,'protected_ids':active[0]['protected_ids'],'active_hypothesis_ids':[],'status':'reserved_not_reviewed'}
 active.append(res);allids={i for r in active for i in r['ids']};assert len(allids)==150
 for r in active:r['other_active_reservations']=sorted(allids-set(r['ids']))
 write('queue.json',rows);write('reserved-ids.json',res);write('active-breadth-reservations.json',active)
 (P/'DECISION.md').write_text('# Root r599 reconciliation\n\nReconciled r596: fifty disjoint literal record reviews, zero proposals or credit. Cumulative coverage is 5,933 record reviews, not complete-statement or whole-corpus technical coverage. Preserve 30 self-contained literal assessments/20 definition-restoration judgments and all prior flags.\n\nThree selected primary passages and one selected successor proof body read. 317193 weak endpoint is a public theorem with strict-wording equality caveats; 319095 exact source conjecture follows in its public source from unaudited measure/variational dependencies. 318548 literal sublattice claim has a short classical Birkhoff/Boolean-block route; bounded-embedding strengthening not claimed. Diagnostic block checks do not earn credit. No full dependency or current registry clearance.\n\nRetain descriptive/corrupt records, source/provenance limits and truncated-output followups. No new HTTP failure or parked-route retry. Root performs administrative integrity/corpus reconciliation only, never upstream or mathematical checkers. Adjudications unchanged.\n\nSol r598 continues. Fifty fresh disjoint records reserved for Sol r600. Exhausted 6,000-row routing expanded to 8,000 via inventory-bound metadata only; adds zero technical reviews. Initial failed routing assertion retained in FAILURES.md. Claude r504 remains rate-limited with fifty reserved unreviewed IDs. No user input pending. Counts remain 9 additional / 39 total / next 40.\n')
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and str(p.relative_to(P)) not in {'manifest.json','verification-receipt.json'}:
   b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'sha256':h(b),'size':len(b)})
 write('manifest.json',{'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':files})
def verify():
 old,data=validate();cov=j(P/'coverage-delta.json');assert len(cov)==5933 and set(cov)==set(old)|{str(d['mathdb_id']) for ds in data.values() for d in ds}
 for k,v in old.items():assert cov[k]==v
 assert cov['344924']['complete_mathematical_statement_reviewed'] is False and cov['344924']['source_restoration_required'] is True
 active=j(P/'active-breadth-reservations.json');seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not set(map(str,ids))&set(cov) and not ids&set(r['protected_ids']);seen|=ids
 assert len(seen)==150
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 assert set(j(P/'reserved-ids.json')['ids'])=={r['mathdb_id'] for r in j(P/'queue.json')}
 route=routing_pool();assert [json.loads(l) for l in (P/'routing-queue.jsonl').open()]==route
 assert (P/'routing-queue.jsonl').read_bytes().startswith((I/'routing-queue.jsonl').read_bytes())
 exact(P,j(P/'manifest.json'))
 try:check(P/'DECISION.md',{'size':0,'sha256':'0'*64})
 except AssertionError:pass
 else:raise AssertionError('negative accepted')
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','coverage':5933,'new_literal_record_reviews':50,'carried_incomplete_statement_ids':[344924],'root_binding_pairs':len(j(P/'bindings.json')),'child_payloads':{name:len(j(F/name/'manifest.json')['files']) for name in data},'original_chunks':20,'frozen_inputs':8,'reservation_disjointness':True,'negative_rejection':True,'scientific_acceptance':False,'counts':{'additional':9,'total':39,'next':40}};write('verification-receipt.json',r);print(json.dumps(r))
if '--build' in sys.argv:build();print('built')
else:verify()
