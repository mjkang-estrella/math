import pathlib,json,hashlib,sys,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;F=P/'frozen';I=F/'root-mathdb-breadth-intake-r513';N='sol-mathdb-primary-qualified-breadth-r512';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),str(p);assert h(b)==e['sha256'],str(p)
def write(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
def exact(root,m):
 assert len(m['files'])==len({e['path'] for e in m['files']})
 assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
 for e in m['files']:check(root/e['path'],e)
def routing_pool():
 old=[json.loads(l) for l in (F/'root-mathdb-breadth-intake-r415/routing-queue.jsonl').open()];oldids={r['mathdb_id'] for r in old};assert len(oldids)==4000
 ref=next(e for e in j(P/'bindings.json') if e['original'].endswith('screening-tags.jsonl'));p=pathlib.Path(ref['original']);check(p,ref)
 extra=[]
 for line in p.open():
  r=json.loads(line)
  if r['mathdb_id'] not in oldids and r.get('status')=='open' and r.get('statement_completeness')=='full':
   extra.append({k:r[k] for k in old[0] if k in r})
 extra.sort(key=lambda r:(-r['review_priority_score'],r['mathdb_id']))
 assert len(extra)>=2000
 out=old+extra[:2000];assert len({r['mathdb_id'] for r in out})==6000
 return out
def validate():
 for e in j(P/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 check(F/N/'manifest.json',{'size':6290,'sha256':'0327d9d877fa2a982823c6c6e33245c4e7afaf07184d1fe43c555977381b5e0f'})
 m=j(F/N/'manifest.json');exact(F/N,m);exact(L/N,m)
 for filename in ['flat-bindings.json']:
  for e in j(F/N/filename):
   if 'path' in e:check(pathlib.Path(e['path']),e)
 exact(L/'root-mathdb-breadth-intake-r513',j(I/'manifest.json'))
 cm=j(F/'pi-mathdb-full-corpus-inventory-r301/manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==3883
 ds=j(F/N/'dispositions.json');ids={d['mathdb_id'] for d in ds};assert len(ds)==len(ids)==50 and ids==set(j(F/'root-mathdb-breadth-intake-r511/reserved-ids.json')['ids']);assert not set(map(str,ids))&set(cov)
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(p,n,r)
 for d in ds:
  p,n,r=found[d['mathdb_id']];assert d['corpus_path']==str(p) and d['line']==n and d['statement']==r['statement'];assert d['statement_sha256']==h(r['statement'].encode());assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert d['discovery_credit']==0
 assert j(F/N/'proposals.json')==[]
 return cov,ds
def build():
 cov,ds=validate()
 for d in ds:cov[str(d['mathdb_id'])]={'source_lane':N,'reported_disposition':d['disposition'],'statement_utf8_sha256':d['statement_sha256'],'canonical_record_sha256':d['canonical_record_sha256'],'accepted_credit':0,'current_registry_cleared':False,'evidence_limit':'Reported literal review; selected source passages only; no full dependency audit','root_reconciled':True}
 write('coverage-delta.json',cov)
 for name in ['adjudications.json','hypothesis-queue.json']:write(name,j(I/name))
 other=[r for r in j(I/'active-breadth-reservations.json') if r['lane']!='sol-mathdb-primary-qualified-breadth-r512']
 other[0]['status']='rate_limited_reserved_unreviewed';other[1]['status']='running'
 blocked=set(map(int,cov))|set(other[0]['ids'])|set(other[1]['ids'])|set(other[0]['protected_ids'])
 route=routing_pool()
 (P/'routing-queue.jsonl').write_text(''.join(json.dumps(r,ensure_ascii=False,sort_keys=True)+'\n' for r in route))
 write('routing-expansion.json',{'prior_rows':4000,'added_rows':2000,'total_rows':6000,'criterion':'Remaining open/full inventory tag records, descending review_priority_score then ascending mathdb_id; automated metadata only','new_technical_reviews':0})
 rows=[r for r in route if r['mathdb_id'] not in blocked][:50];assert len(rows)==50,'routing pool needs expansion'
 ids=[r['mathdb_id'] for r in rows];write('queue.json',rows)
 res={'lane':'sol-mathdb-primary-qualified-breadth-r516','ids':ids,'other_active_reservations':other[0]['ids']+other[1]['ids'],'protected_ids':other[0]['protected_ids'],'active_hypothesis_ids':[],'coverage_baseline':3933,'status':'reserved_not_reviewed'}
 write('reserved-ids.json',res);write('active-breadth-reservations.json',other+[res])
 (P/'DECISION.md').write_text("# Root r515 reconciliation\n\nReconcile r512: fifty disjoint literal reviews, eight selected primary-passage rows, zero proposals/credit. Latest coverage becomes 3,933 reported literal reviews. Child's older 3,833 assignment baseline is superseded by cumulative root reconciliation. No whole-body, dependency or current-registry clearance.\n\nPreserve source-known/routine exclusions 357226 and 357065, endpoint/convention exclusions 357683 and 356681, and other technical HOLDs. Published enumeration diagnostics do not create discovery credit. Preserve two corrected helper failures, extraction/access limits, and pre-binding display of two unrelated corpus records; successful later hashing does not cure timing deviations.\n\nClaude r504 remains rate-limited with fifty unreviewed reserved records. Sol r514 continues. Reserve next disjoint fifty for Sol r516. Existing adjudications and counts 9 additional /39 total /next40 remain unchanged. Root performs administrative/file/corpus reconciliation only. Integrity PASS is not mathematical or novelty acceptance.\n")
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and str(p.relative_to(P)) not in {'manifest.json','verification-receipt.json'}:
   b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'sha256':h(b),'size':len(b)})
 write('manifest.json',{'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':files})
def verify():
 old,ds=validate();cov=j(P/'coverage-delta.json');assert len(cov)==3933 and set(cov)==set(old)|{str(d['mathdb_id']) for d in ds}
 route=routing_pool();assert [json.loads(l) for l in (P/'routing-queue.jsonl').open()]==route
 for k,v in old.items():assert cov[k]==v
 seen=set()
 for r in j(P/'active-breadth-reservations.json'):
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not set(map(str,ids))&set(cov) and not ids&set(r['protected_ids']);seen|=ids
 assert len(seen)==150
 assert set(j(P/'reserved-ids.json')['ids'])=={r['mathdb_id'] for r in j(P/'queue.json')}
 exact(P,j(P/'manifest.json'))
 try:check(P/'DECISION.md',{'size':0,'sha256':'0'*64})
 except AssertionError:pass
 else:raise AssertionError('negative accepted')
 receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','coverage':3933,'new_literal_reviews':50,'root_binding_pairs':len(j(P/'bindings.json')),'child_payloads':len(j(F/N/'manifest.json')['files']),'original_chunks':20,'frozen_inputs':8,'reservation_disjointness':True,'negative_rejection':True,'scientific_acceptance':False,'counts':{'additional':9,'total':39,'next':40}}
 write('verification-receipt.json',receipt);print(json.dumps(receipt))
if '--build' in sys.argv:build();print('built')
else:verify()
