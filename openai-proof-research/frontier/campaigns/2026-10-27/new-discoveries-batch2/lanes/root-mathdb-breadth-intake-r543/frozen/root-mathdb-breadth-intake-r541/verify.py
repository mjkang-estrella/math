import pathlib,json,hashlib,sys,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;F=P/'frozen';I=F/'root-mathdb-breadth-intake-r539';C=L/'pi-mathdb-full-corpus-inventory-r301'
SPEC=[('sol-mathdb-primary-qualified-breadth-r538',6093,'6b01fd4b7be188dd453caa6c80441dd497493e8329bc45339aa05d6bd1b4c119','root-mathdb-breadth-intake-r537/reserved-ids.json','corpus_chunk','line','statement_sha256')]
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
 exact(L/'root-mathdb-breadth-intake-r539',j(I/'manifest.json'))
 cm=j(F/'pi-mathdb-full-corpus-inventory-r301/manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==4433
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
 write('coverage-delta.json',cov)
 for n in ['adjudications.json','hypothesis-queue.json']:write(n,j(I/n))
 active=[r for r in j(I/'active-breadth-reservations.json') if r['lane']!='sol-mathdb-primary-qualified-breadth-r538']
 blocked=set(map(int,cov))|{i for r in active for i in r['ids']}|set(active[0]['protected_ids'])
 route=[json.loads(l) for l in (I/'routing-queue.jsonl').open()];assert len(route)==6000
 (P/'routing-queue.jsonl').write_bytes((I/'routing-queue.jsonl').read_bytes())
 rows=[r for r in route if r['mathdb_id'] not in blocked][:50];assert len(rows)==50
 res={'lane':'sol-mathdb-primary-qualified-breadth-r542','ids':[r['mathdb_id'] for r in rows],'coverage_baseline':4483,'protected_ids':active[0]['protected_ids'],'active_hypothesis_ids':[],'status':'reserved_not_reviewed'}
 active.append(res);allids={i for r in active for i in r['ids']};assert len(allids)==150
 for r in active:r['other_active_reservations']=sorted(allids-set(r['ids']))
 write('queue.json',rows);write('reserved-ids.json',res);write('active-breadth-reservations.json',active)
 (P/'DECISION.md').write_text("# Root r541 reconciliation\n\nReconciled r538: fifty disjoint reported literal reviews, forty-five HOLDs, five public-source exclusions, zero proposals. Cumulative literal coverage is 4,483, not full technical or novelty coverage. Six selected records inspected in eight primary/successor HTML bodies; no whole-body, dependency or registry clearance.\n\nReported source exclusions: 376377 Hoffman-Singleton counterexample; 376634 Fekete aperture theorem; 377820 strongly MDS code existence; 378061 Hom-complex connectivity subsumption; 378394 Chung discrepancy refutation. Preserve each row's evidence limits. In particular 378061 retains an exact-primary-version gap and a finite-simple-graph scope bridge; full dependency audits remain absent. Root does not upgrade these to independently audited mathematical conclusions. The public graph certificate is uncredited and was not executed by root.\n\nPreserve the failed bs4 extraction and subsequent missing-file search. Current registry and novelty remain HOLD. Carry existing adjudications unchanged. Root performs only file, corpus and assignment reconciliation, no upstream verifier or mathematical execution.\n\nSol r540 continues. Reserve fifty fresh disjoint records for Sol r542. Claude r504 remains rate-limited with its fifty IDs reserved/unreviewed. Counts remain 9 additional / 39 total / next 40.\n")
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and str(p.relative_to(P)) not in {'manifest.json','verification-receipt.json'}:
   b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'sha256':h(b),'size':len(b)})
 write('manifest.json',{'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':files})
def verify():
 old,data=validate();cov=j(P/'coverage-delta.json');assert len(cov)==4483 and set(cov)==set(old)|{str(d['mathdb_id']) for ds in data.values() for d in ds}
 for k,v in old.items():assert cov[k]==v
 active=j(P/'active-breadth-reservations.json');seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not set(map(str,ids))&set(cov) and not ids&set(r['protected_ids']);seen|=ids
 assert len(seen)==150
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 assert set(j(P/'reserved-ids.json')['ids'])=={r['mathdb_id'] for r in j(P/'queue.json')}
 assert (P/'routing-queue.jsonl').read_bytes()==(I/'routing-queue.jsonl').read_bytes()
 exact(P,j(P/'manifest.json'))
 try:check(P/'DECISION.md',{'size':0,'sha256':'0'*64})
 except AssertionError:pass
 else:raise AssertionError('negative accepted')
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','coverage':4483,'new_literal_reviews':50,'root_binding_pairs':len(j(P/'bindings.json')),'child_payloads':{name:len(j(F/name/'manifest.json')['files']) for name in data},'original_chunks':20,'frozen_inputs':8,'reservation_disjointness':True,'negative_rejection':True,'scientific_acceptance':False,'counts':{'additional':9,'total':39,'next':40}};write('verification-receipt.json',r);print(json.dumps(r))
if '--build' in sys.argv:build();print('built')
else:verify()
