import pathlib,json,hashlib,sys,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;F=P/'frozen';I=F/'root-mathdb-breadth-intake-r523';C=L/'pi-mathdb-full-corpus-inventory-r301'
SPEC=[('sol-mathdb-primary-qualified-breadth-r522',6270,'423482c4ea0b8038811a1cf7296950209cae977acfc3964a046713d329472cfa','root-mathdb-breadth-intake-r519/reserved-ids-r522.json','corpus_chunk','corpus_line','statement_utf8_sha256')]
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
 exact(L/'root-mathdb-breadth-intake-r523',j(I/'manifest.json'))
 cm=j(F/'pi-mathdb-full-corpus-inventory-r301/manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==4133
 data={};allids=set()
 for name,size,sha,res,ck,lk,hk in SPEC:
  check(F/name/'manifest.json',{'size':size,'sha256':sha});m=j(F/name/'manifest.json');exact(F/name,m);exact(L/name,m)
  for e in j(F/name/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
  ds=j(F/name/'dispositions.json');ids={d['mathdb_id'] for d in ds};assert len(ds)==len(ids)==50 and ids==set(j(F/res)['ids']);assert not ids&allids and not set(map(str,ids))&set(cov);allids|=ids;data[name]=ds
  proposals=j(F/name/'proposals.json');assert len(proposals)==2 and {p['mathdb_id'] for p in proposals}=={365437,366370}
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
 active=[r for r in j(I/'active-breadth-reservations.json') if r['lane']!='sol-mathdb-primary-qualified-breadth-r522']
 allids={i for r in active for i in r['ids']};assert len(allids)==100
 for r in active:r['other_active_reservations']=sorted(allids-set(r['ids']));r['active_hypothesis_ids']=[366370];r['protected_ids']=sorted(set(r['protected_ids'])|{366370,365437,365439})
 write('active-breadth-reservations.json',active)
 (P/'routing-queue.jsonl').write_bytes((I/'routing-queue.jsonl').read_bytes())
 hypotheses=j(I/'hypothesis-queue.json')
 hypotheses += [{'mathdb_id':366370,'status':'assigned_independent_source_prior_math_review','lane':'sol-mathdb-ordinal-balls-preliminary-review-r526','credit':0},{'mathdb_id':365437,'related_ids':[365439],'one_family':True,'status':'queued_source_first_independent_review','credit':0}]
 write('hypothesis-queue.json',hypotheses)
 write('candidate-briefs.json',j(F/SPEC[0][0]/'proposals.json'))
 (P/'DECISION.md').write_text("# Root r525 candidate intake\n\nReconcile r522's fifty literal reviews with exact corpus hashes and assignment. Latest coverage4,183 reported literal reviews; two conditional family briefs, zero acceptance/credit. Root has not executed mathematical checkers or certified either claimed counterexample. Existing counts9additional/39total/next40 unchanged.\n\nRoute366370 first: reported four-point ordinal rank matrix with nine balls below ten is a very small full-scope negation candidate. Source axioms, ball conventions, distinctness quantifiers, entire source-internal boundary and closest prior/successor bodies require independent qualification. Metric lifting itself is source Proposition1.5 and earns no credit. Allocate separate Sol r526 review; no Lean or manuscript now.\n\nQueue365437/365439 together as one stack-fiber family for a separate source-first review when a Sol slot opens. Candidate reports n5 second-largest fiber5 rather than4, and n8 tie64 at a distinct output defeating uniqueness. Source transition convention and actual journal version may change the scope; published Discrete Mathematics349(3),114834 is metadata-only, typeset body unread. No formal investment or novelty claim. Do not bundle its mathematics into the ordinal review.\n\nPreserve limited four-primary selected-passage coverage, predecessor-versus-successor version issue for Echeloned Spaces, missing bs4, stopped404 and truncated displays. Other r522 exclusions are known-source/wording-only and earn no credit. No current registry clearance. Root adopts no mathematical verdict from an integrity receipt.\n\nSol r524 breadth continues. Claude r504 remains rate-limited/unreviewed with its reservation protected. New focused Sol r526 makes two active Sol delegates total. No new breadth allocation until the next useful slot; unchanged6000metadata routing pool retained. Root continues only orchestration and administrative/hash reconciliation.\n")
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and str(p.relative_to(P)) not in {'manifest.json','verification-receipt.json'}:
   b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'sha256':h(b),'size':len(b)})
 write('manifest.json',{'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':files})
def verify():
 old,data=validate();cov=j(P/'coverage-delta.json');assert len(cov)==4183 and set(cov)==set(old)|{str(d['mathdb_id']) for ds in data.values() for d in ds}
 for k,v in old.items():assert cov[k]==v
 active=j(P/'active-breadth-reservations.json');seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not set(map(str,ids))&set(cov) and not ids&set(r['protected_ids']);seen|=ids
 assert len(seen)==100
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 assert {p['mathdb_id'] for p in j(P/'candidate-briefs.json')}=={365437,366370}
 assert (P/'routing-queue.jsonl').read_bytes()==(I/'routing-queue.jsonl').read_bytes()
 exact(P,j(P/'manifest.json'))
 try:check(P/'DECISION.md',{'size':0,'sha256':'0'*64})
 except AssertionError:pass
 else:raise AssertionError('negative accepted')
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','coverage':4183,'new_literal_reviews':50,'root_binding_pairs':len(j(P/'bindings.json')),'child_payloads':{name:len(j(F/name/'manifest.json')['files']) for name in data},'original_chunks':20,'frozen_inputs':8,'reservation_disjointness':True,'negative_rejection':True,'scientific_acceptance':False,'counts':{'additional':9,'total':39,'next':40}};write('verification-receipt.json',r);print(json.dumps(r))
if '--build' in sys.argv:build();print('built')
else:verify()
