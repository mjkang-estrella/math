import pathlib,json,hashlib,sys,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;F=P/'frozen';I=F/'root-mathdb-breadth-intake-r509';N='sol-mathdb-primary-qualified-breadth-r508';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),str(p);assert h(b)==e['sha256'],str(p)
def write(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
def exact(root,m):
 assert len(m['files'])==len({e['path'] for e in m['files']})
 assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
 for e in m['files']:check(root/e['path'],e)
def validate():
 for e in j(P/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 check(F/N/'manifest.json',{'size':3936,'sha256':'37713b1e05dad5511d032caf8527ecb4b4fa3fd094c7b746e6cc60feb54fccac'})
 m=j(F/N/'manifest.json');exact(F/N,m);exact(L/N,m)
 for filename in ['initial-bindings.json','flat-bindings.json']:
  for e in j(F/N/filename):
   if 'path' in e:check(pathlib.Path(e['path']),e)
 exact(L/'root-mathdb-breadth-intake-r509',j(I/'manifest.json'))
 cm=j(F/'pi-mathdb-full-corpus-inventory-r301/manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==3783
 ds=j(F/N/'dispositions.json');ids={d['ID'] for d in ds};assert len(ds)==len(ids)==50 and ids==set(j(F/'root-mathdb-banzhaf-retirement-intake-r503/reserved-ids-r508.json')['ids']);assert not set(map(str,ids))&set(cov)
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(p,n,r)
 for d in ds:
  p,n,r=found[d['ID']];assert d['chunk']==str(p) and d['line']==n and d['literal']==r['statement'];assert d['statement_utf8_sha256']==h(r['statement'].encode());assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert d['accepted_credit']==0
 assert j(F/N/'proposals.json')==[]
 return cov,ds
def build():
 cov,ds=validate()
 for d in ds:cov[str(d['ID'])]={'source_lane':N,'reported_disposition':d['disposition'],'statement_utf8_sha256':d['statement_utf8_sha256'],'canonical_record_sha256':d['canonical_record_sha256'],'accepted_credit':0,'current_registry_cleared':False,'evidence_limit':'Reported literal review; selected source passages only; no full dependency audit','root_reconciled':True}
 write('coverage-delta.json',cov)
 for name in ['adjudications.json','hypothesis-queue.json']:write(name,j(I/name))
 other=[r for r in j(I/'active-breadth-reservations.json') if r['lane']!='sol-mathdb-primary-qualified-breadth-r508']
 other[0]['status']='rate_limited_reserved_unreviewed';other[1]['status']='running'
 blocked=set(map(int,cov))|set(other[0]['ids'])|set(other[1]['ids'])|set(other[0]['protected_ids'])
 route=[json.loads(l) for l in (F/'root-mathdb-breadth-intake-r415/routing-queue.jsonl').open()]
 rows=[r for r in route if r['mathdb_id'] not in blocked][:50];assert len(rows)==50,'routing pool needs expansion'
 ids=[r['mathdb_id'] for r in rows];write('queue.json',rows)
 res={'lane':'sol-mathdb-primary-qualified-breadth-r512','ids':ids,'other_active_reservations':other[0]['ids']+other[1]['ids'],'protected_ids':other[0]['protected_ids'],'active_hypothesis_ids':[],'coverage_baseline':3833,'status':'reserved_not_reviewed'}
 write('reserved-ids.json',res);write('active-breadth-reservations.json',other+[res])
 (P/'DECISION.md').write_text('# Root r511 reconciliation\n\nReconcile r508: exactly fifty new literal reviews, zero proposals and no credit. Coverage becomes 3,833 reported literal reviews; this is not full primary/proof/novelty coverage. Preserve three source-stated full-target exclusions (383495,392481,405217); 383344 remains HOLD_PUBLIC_PROOF because Eulerian convention and partial proof coverage are insufficient. Other rows remain HOLD/PARK. Four primary bodies inspected (two complete extracted local mathematical bodies, two partial); finite diagnostics are not proofs. Font/extraction warnings and truncated displays remain disclosed.\n\nClaude r504 remains rate-limited with fifty unreviewed reserved IDs. Sol r510 continues. New Sol r512 receives the next disjoint fifty. Existing r509 adjudications carry unchanged; no scientific upgrades or root mathematics. Counts stay 9 additional /39 total /next40. Root verifies immutable inputs, assignment, literal/canonical hashes and exact file membership only. No upstream verifier execution, MathDB requests or shared scientific changes.\n')
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and str(p.relative_to(P)) not in {'manifest.json','verification-receipt.json'}:
   b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'sha256':h(b),'size':len(b)})
 write('manifest.json',{'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':files})
def verify():
 old,ds=validate();cov=j(P/'coverage-delta.json');assert len(cov)==3833 and set(cov)==set(old)|{str(d['ID']) for d in ds}
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
 receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','coverage':3833,'new_literal_reviews':50,'root_binding_pairs':len(j(P/'bindings.json')),'child_payloads':len(j(F/N/'manifest.json')['files']),'original_chunks':20,'frozen_inputs':8,'reservation_disjointness':True,'negative_rejection':True,'scientific_acceptance':False,'counts':{'additional':9,'total':39,'next':40}}
 write('verification-receipt.json',receipt);print(json.dumps(receipt))
if '--build' in sys.argv:build();print('built')
else:verify()
