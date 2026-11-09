import pathlib,json,hashlib,sys,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;F=P/'frozen';I=F/'root-mathdb-breadth-intake-r517';C=L/'pi-mathdb-full-corpus-inventory-r301'
SPEC=[('sol-mathdb-primary-qualified-breadth-r516',5214,'09e0712f6b7e7619365fec549e9f2c1b4cbc9c2f77f5d1ff57a0c39d5a224258','root-mathdb-breadth-intake-r515/reserved-ids.json','chunk','line','statement_sha256'),('sol-mathdb-primary-qualified-breadth-r518',4647,'36aaaee0fdd562ab6d368837139e5c8566cd420e7e371b5e39cf5c0c5519146c','root-mathdb-breadth-intake-r517/reserved-ids.json','corpus_chunk','corpus_line','statement_utf8_sha256')]
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
 exact(L/'root-mathdb-breadth-intake-r517',j(I/'manifest.json'))
 cm=j(F/'pi-mathdb-full-corpus-inventory-r301/manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==3983
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
 assert len(found)==100
 for name,_,_,_,ck,lk,hk in SPEC:
  for d in data[name]:
   p,n,r=found[d['mathdb_id']];assert d[ck]==str(p) and d[lk]==n and d['statement']==r['statement'];assert d[hk]==h(r['statement'].encode());assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert d['accepted_credit']==0
 return cov,data
def build():
 cov,data=validate()
 for name,_,_,_,_,_,hk in SPEC:
  for d in data[name]:cov[str(d['mathdb_id'])]={'source_lane':name,'reported_disposition':d['disposition'],'statement_utf8_sha256':d[hk],'canonical_record_sha256':d['canonical_record_sha256'],'accepted_credit':0,'current_registry_cleared':False,'root_reconciled':True,'evidence_limit':'Reported literal review; selected source readings and finite checks not upgraded to complete proof/novelty audits'}
 write('coverage-delta.json',cov)
 for n in ['adjudications.json','hypothesis-queue.json']:write(n,j(I/n))
 claude=next(r for r in j(I/'active-breadth-reservations.json') if r['lane']=='claude-mathdb-primary-qualified-breadth-r504');claude['status']='rate_limited_reserved_unreviewed'
 blocked=set(map(int,cov))|set(claude['ids'])|set(claude['protected_ids'])
 route=[json.loads(l) for l in (I/'routing-queue.jsonl').open()];assert len(route)==6000
 (P/'routing-queue.jsonl').write_bytes((I/'routing-queue.jsonl').read_bytes())
 rows=[r for r in route if r['mathdb_id'] not in blocked][:100];assert len(rows)==100
 active=[claude]
 for i,num in enumerate([520,522]):
  batch=rows[50*i:50*(i+1)];res={'lane':f'sol-mathdb-primary-qualified-breadth-r{num}','ids':[r['mathdb_id'] for r in batch],'coverage_baseline':4083,'protected_ids':claude['protected_ids'],'active_hypothesis_ids':[],'status':'reserved_not_reviewed'}
  write(f'queue-r{num}.json',batch);active.append(res)
 allids={i for r in active for i in r['ids']};assert len(allids)==150
 for r in active:r['other_active_reservations']=sorted(allids-set(r['ids']))
 for r in active[1:]:write('reserved-ids-'+r['lane'].rsplit('-',1)[-1]+'.json',r)
 write('active-breadth-reservations.json',active)
 (P/'DECISION.md').write_text('''# Root r519 reconciliation

Reconcile r516 and r518 together: 100 disjoint literal reviews, zero proposals or credit. Coverage becomes 4,083 reported literal reviews. Their older individual assignment baselines are superseded by this union. No complete technical corpus or novelty coverage is claimed. Counts remain 9 additional /39 total /next40.

r516: source 359499 publicly refutes its target; 360358 is a definition mismatch. Records 361256/361257 share conjectural scope: both statements read, not two novel problems. Preserve r304 objections for359807. GF(2)158cases are diagnostics only. The35-variable MILP aborted before any result; no certificate inferred or retry authorized. Five primaries/one successor selected, only star-critical Ramsey complete extracted body; dependencies unread. Preserve pre-binding admin/schema display and premature exploratory computation deviation.

r518:49HOLDs, one source-acknowledged wording/endpoint exclusion. Four primary HTML bodies selected; no full dependency/successor/registry clearance. Two reported public resolutions remain body-unchecked, not audited retirements. Preserve rebinding-import error, pre-binding admin/provenance reading and truncated broad displays. Finite bisection check refutes only a shortcut.

Reserve fresh disjoint50-record batches Sol r520/r522 from unchanged6,000-row metadata pool. Claude r504 remains rate-limited with50reserved unreviewed. Both prior Sol tasks completed. Root continues only orchestration/administrative/hash/corpus reconciliation, no mathematics or upstream verifier execution. Integrity is not mathematics/novelty acceptance.
''')
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and str(p.relative_to(P)) not in {'manifest.json','verification-receipt.json'}:
   b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'sha256':h(b),'size':len(b)})
 write('manifest.json',{'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':files})
def verify():
 old,data=validate();cov=j(P/'coverage-delta.json');assert len(cov)==4083 and set(cov)==set(old)|{str(d['mathdb_id']) for ds in data.values() for d in ds}
 for k,v in old.items():assert cov[k]==v
 active=j(P/'active-breadth-reservations.json');seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not set(map(str,ids))&set(cov) and not ids&set(r['protected_ids']);seen|=ids
 assert len(seen)==150
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 for num in [520,522]:assert set(j(P/f'reserved-ids-r{num}.json')['ids'])=={r['mathdb_id'] for r in j(P/f'queue-r{num}.json')}
 assert (P/'routing-queue.jsonl').read_bytes()==(I/'routing-queue.jsonl').read_bytes()
 exact(P,j(P/'manifest.json'))
 try:check(P/'DECISION.md',{'size':0,'sha256':'0'*64})
 except AssertionError:pass
 else:raise AssertionError('negative accepted')
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','coverage':4083,'new_literal_reviews':100,'root_binding_pairs':len(j(P/'bindings.json')),'child_payloads':{name:len(j(F/name/'manifest.json')['files']) for name in data},'original_chunks':20,'frozen_inputs':8,'reservation_disjointness':True,'negative_rejection':True,'scientific_acceptance':False,'counts':{'additional':9,'total':39,'next':40}};write('verification-receipt.json',r);print(json.dumps(r))
if '--build' in sys.argv:build();print('built')
else:verify()
