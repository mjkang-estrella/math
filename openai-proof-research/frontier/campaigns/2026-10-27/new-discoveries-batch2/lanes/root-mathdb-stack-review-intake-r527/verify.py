import pathlib,json,hashlib,sys,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;F=P/'frozen';I=F/'root-mathdb-candidate-intake-r525';C=L/'pi-mathdb-full-corpus-inventory-r301'
SPEC=[('sol-mathdb-primary-qualified-breadth-r524',4814,'3584ab2e1b672cd2764aa74eff1f3732efffe280dddf03e00670f5e08d4b0fde','root-mathdb-breadth-intake-r523/reserved-ids.json','corpus_chunk','corpus_line','statement_sha256')]
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
 exact(L/'root-mathdb-candidate-intake-r525',j(I/'manifest.json'))
 cm=j(F/'pi-mathdb-full-corpus-inventory-r301/manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==4183
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
   p,n,r=found[d['mathdb_id']];assert d[ck]==str(p) and d[lk]==n and d['literal_statement']==r['statement'];assert d[hk]==h(r['statement'].encode());assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert d['credit']==0
 return cov,data
def build():
 cov,data=validate()
 for name,_,_,_,_,_,hk in SPEC:
  for d in data[name]:cov[str(d['mathdb_id'])]={'source_lane':name,'reported_disposition':d['disposition'],'statement_utf8_sha256':d[hk],'canonical_record_sha256':d['canonical_record_sha256'],'accepted_credit':0,'current_registry_cleared':False,'root_reconciled':True,'evidence_limit':'Reported literal review; selected source readings and finite checks not upgraded to complete proof/novelty audits'}
 write('coverage-delta.json',cov)
 for n in ['adjudications.json','hypothesis-queue.json']:write(n,j(I/n))
 active=[r for r in j(I/'active-breadth-reservations.json') if r['lane']!='sol-mathdb-primary-qualified-breadth-r524']
 assert len(active)==1 and active[0]['lane']=='claude-mathdb-primary-qualified-breadth-r504'
 active[0]['other_active_reservations']=[];active[0]['active_hypothesis_ids']=[366370,365437,365439]
 write('active-breadth-reservations.json',active)
 (P/'routing-queue.jsonl').write_bytes((I/'routing-queue.jsonl').read_bytes())
 hypotheses=j(I/'hypothesis-queue.json')
 for q in hypotheses:
  if q['mathdb_id']==365437:q['status']='assigned_source_first_independent_review';q['lane']='sol-mathdb-stack-fiber-preliminary-review-r528'
 write('hypothesis-queue.json',hypotheses);write('candidate-briefs.json',j(I/'candidate-briefs.json'))
 (P/'DECISION.md').write_text('# Root r527 reconciliation and stack review assignment\n\nReconcile r524:fifty disjoint literal reviews,zero proposals. Latest coverage4,233; child used assigned older4,133 baseline.368923 is reported source-theorem refutation from selected proof,not a complete dependency audit. Five target records selected across four arXivv1HTML bodies; no whole-body,successor,registry clearance. Finite information-state diagnostic at excluded threshold is not a counterexample. Preserve parser failure and pre-verification metadata/unassigned-row display deviation. Counts9additional/39total/next40 unchanged.\n\nAssign separate Sol r528 source-first independent review of365437/365439 as one stack-fiber family. Producer r522 reports n5second-largest5 rather than4 and n8tie64 defeating uniqueness. Exact stack reading/vincular adjacency, whole-source internal claims and actual published journal wording are critical. Journal DOI10.1016/j.disc.2025.114834 metadata alone does not authenticate conjecture survival. No Lean/manuscript or new-credit claim. Producer source/checkers retained as data; root does not run mathematical code.\n\nSol r526 ordinal-ball review continues separately. Claude r504 remains rate-limited/reserved unreviewed. Both Sol slots now carry bounded candidate reviews; return the next freed useful slot to breadth unless an eligible small result justifies a distinct follow-up. Protected candidates and existing adjudications unchanged. Routing6000rows remains metadata only; integrity never proves mathematical/novelty acceptance.\n')
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and str(p.relative_to(P)) not in {'manifest.json','verification-receipt.json'}:
   b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'sha256':h(b),'size':len(b)})
 write('manifest.json',{'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':files})
def verify():
 old,data=validate();cov=j(P/'coverage-delta.json');assert len(cov)==4233 and set(cov)==set(old)|{str(d['mathdb_id']) for ds in data.values() for d in ds}
 for k,v in old.items():assert cov[k]==v
 active=j(P/'active-breadth-reservations.json');seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not set(map(str,ids))&set(cov) and not ids&set(r['protected_ids']);seen|=ids
 assert len(seen)==50
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 assert {p['mathdb_id'] for p in j(P/'candidate-briefs.json')}=={365437,366370}
 assert (P/'routing-queue.jsonl').read_bytes()==(I/'routing-queue.jsonl').read_bytes()
 exact(P,j(P/'manifest.json'))
 try:check(P/'DECISION.md',{'size':0,'sha256':'0'*64})
 except AssertionError:pass
 else:raise AssertionError('negative accepted')
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','coverage':4233,'new_literal_reviews':50,'root_binding_pairs':len(j(P/'bindings.json')),'child_payloads':{name:len(j(F/name/'manifest.json')['files']) for name in data},'original_chunks':20,'frozen_inputs':8,'reservation_disjointness':True,'negative_rejection':True,'scientific_acceptance':False,'counts':{'additional':9,'total':39,'next':40}};write('verification-receipt.json',r);print(json.dumps(r))
if '--build' in sys.argv:build();print('built')
else:verify()
