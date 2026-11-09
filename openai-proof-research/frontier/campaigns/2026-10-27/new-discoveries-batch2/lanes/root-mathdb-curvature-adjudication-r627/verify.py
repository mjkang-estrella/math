import pathlib,json,hashlib,sys,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;F=P/'frozen';I=F/'root-mathdb-breadth-intake-r625';C=L/'pi-mathdb-full-corpus-inventory-r301';R='claude-mathdb-curvature-prior-review-r618'
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
 exact(L/'root-mathdb-breadth-intake-r625',j(I/'manifest.json'))
 for e in j(L/'root-mathdb-breadth-intake-r625/bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 check(F/R/'manifest.json',{'size':7555,'sha256':'c3875010d4faa2e503f787fc15de30e4ef9679812ffb0938af56f803479b0eec'})
 exact(F/R,j(F/R/'manifest.json'));exact(L/R,j(F/R/'manifest.json'))
 for e in j(F/R/'flat-bindings.json')['refs']:check(L/e['path'],e)
 receipt=j(F/R/'final-receipt.json');assert receipt['verify_py']['exit']==0
 cm=j(F/'pi-mathdb-full-corpus-inventory-r301/manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==6583;return cov
NOTE="""# Root r627 curvature credit adjudication

Adopt the independent review's recommendation to EXCLUDE338366 from additional-discovery credit as a routine deduction from a prior public graph. This is a credit decision, not a claim that an explicitly named refutation was published or that current MathDB status changed. Reviewer reports independent exact validation of the candidate and the reconstructed Bai-Lu-Yau graph. Root performs no new mathematical proof work.

Material limits remain explicit: the published text/figure require two degree-inconsistent defects to be reconciled; the reviewer calls reconstruction risk low-to-moderate. Both journal bodies remain unread. Idleness-conversion theorem is cited, not fully audited; direct finite checker is independently authored but not rerun at root. No infinite4-regular counterexample established. Do not upgrade these limitations to clean literal-object or complete-prior clearance. Registry remains HOLD. Candidate differs as a weaker witness of the same negation; no Lean/manuscript or further focused investment.338408 remains parked on endpoint objection.

Preserve all reviewer failures, including roughly ten unguarded administrative Python snippets. Integrity PASS does not erase procedural deviations or establish mathematical/novelty PASS. IMRN DOI10.1093/imrn/rnz305 resolved to HTTP403 challenge; that route is now parked, no retry or alternative-route fishing. AJM landing page shell did not provide a body.

Coverage stays6,583 literal record reviews; no new record review credit for this focused adjudication. Counts unchanged9additional39totalnext40. Sol r624/r626 continue. Fresh Claude r628 breadth assignment uses queue-r628.json/reserved-ids-r628.json. Three disjoint breadth reservations; no active focused hypothesis. Preserve protected338366/338408. Routing8,000metadata rows stays uncredited. Generic outbound headers/privacy and earlier access stops unchanged. No input needed.
"""
def build():
 cov=validate();write('coverage-delta.json',cov)
 adj=j(I/'adjudications.json');adj['338366']={'credit':0,'disposition':'EXCLUDE_ROUTINE_PUBLISHED_OBJECT_BRIDGE','review':R+'/review.md','mathematics':'Independent reviewer reports exact validation; not root mathematical replay','prior_scope':'Bai-Lu-Yau arXiv2103.00941v2 Theorem11/Figure35 plus curvature-convention and sphere-count bridge','qualification':'Published object reconstructed modulo two text/figure defects; journal bodies unread; direct exact reviewer checker retained; no explicitly named prior refutation established','current_registry_cleared':False,'procedural_limits':'Unguarded administrative snippets disclosed'};write('adjudications.json',adj)
 hyp=j(I/'hypothesis-queue.json')
 for r in hyp:
  if r['mathdb_id']==338366:r.update({'status':'EXCLUDE_ROUTINE_PUBLISHED_OBJECT_BRIDGE','review':R+'/review.md'})
 write('hypothesis-queue.json',hyp);write('focused-assignment.json',{'active':False,'mathdb_id':338366,'status':'completed_excluded_from_credit','review':R+'/review.md'})
 active=j(I/'active-breadth-reservations.json');blocked=set(map(int,cov))|{i for r in active for i in r['ids']}|set(active[0]['protected_ids']);route=[json.loads(l) for l in (I/'routing-queue.jsonl').open()];assert len(route)==8000
 (P/'routing-queue.jsonl').write_bytes((I/'routing-queue.jsonl').read_bytes());rows=[r for r in route if r['mathdb_id'] not in blocked][:50];assert len(rows)==50
 res={'lane':'claude-mathdb-primary-qualified-breadth-r628','ids':[r['mathdb_id'] for r in rows],'coverage_baseline':6583,'protected_ids':active[0]['protected_ids'],'active_hypothesis_ids':[],'status':'reserved_not_reviewed'};active.append(res);ids={i for r in active for i in r['ids']};assert len(ids)==150
 for r in active:r['other_active_reservations']=sorted(ids-set(r['ids']));r['active_hypothesis_ids']=[]
 write('queue-r628.json',rows);write('reserved-ids-r628.json',res);write('active-breadth-reservations.json',active);(P/'DECISION.md').write_text(NOTE)
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and str(p.relative_to(P)) not in {'manifest.json','verification-receipt.json'}:
   b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'size':len(b),'sha256':h(b)})
 write('manifest.json',{'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':files})
def verify():
 old=validate();assert j(P/'coverage-delta.json')==old
 active=j(P/'active-breadth-reservations.json');seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not set(map(str,ids))&set(old) and not ids&set(r['protected_ids']);assert not r['active_hypothesis_ids'];seen|=ids
 assert len(seen)==150
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 assert set(j(P/'reserved-ids-r628.json')['ids'])=={r['mathdb_id'] for r in j(P/'queue-r628.json')}
 assert (P/'routing-queue.jsonl').read_bytes()==(I/'routing-queue.jsonl').read_bytes();exact(P,j(P/'manifest.json'))
 try:check(P/'DECISION.md',{'size':0,'sha256':'0'*64})
 except AssertionError:pass
 else:raise AssertionError('negative accepted')
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','coverage':6583,'new_literal_record_reviews':0,'review_payloads':len(j(F/R/'manifest.json')['files']),'root_binding_pairs':len(j(P/'bindings.json')),'original_chunks':20,'frozen_inputs':8,'reservation_disjointness':True,'negative_rejection':True,'scientific_acceptance':False,'credit_decision':'EXCLUDE338366 with stated reconstruction/journal/registry limitations','counts':{'additional':9,'total':39,'next':40}};write('verification-receipt.json',r);print(json.dumps(r))
if '--build' in sys.argv:build();print('built')
else:verify()
