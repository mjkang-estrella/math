import pathlib,json,hashlib,sys,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;F=P/'frozen';I=F/'root-mathdb-ordinal-exclusion-intake-r529';N='sol-mathdb-stack-fiber-preliminary-review-r528';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),str(p);assert h(b)==e['sha256'],str(p)
def write(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
def exact(root,m):
 names={e['path'] for e in m['files']};assert len(names)==len(m['files']);assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==names
 for e in m['files']:check(root/e['path'],e)
def validate():
 for e in j(P/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 check(F/N/'manifest.json',{'size':7130,'sha256':'9d8abad7bd8ba94ca5745d191af88a9017563f3f94d433289f8190f884dc52db'})
 m=j(F/N/'manifest.json');exact(F/N,m);exact(L/N,m)
 for e in j(F/N/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 exact(L/'root-mathdb-ordinal-exclusion-intake-r529',j(I/'manifest.json'))
 cm=j(F/'pi-mathdb-full-corpus-inventory-r301/manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==4233
 return cov
def build():
 cov=validate();write('coverage-delta.json',cov)
 adj=j(I/'adjudications.json');adj['365437']={'related_ids':[365439],'one_family':True,'disposition':'PARK_SOURCE_PRIOR_HOLD','credit':0,'review':N+'/review.md','math_status':'Independent ordinary PASS against arXiv2410.17057v1; no root mathematical replay','source_scope':'SC_(1 underline23),second-largest distinct fiber claim n>=3; n5 sizes8 and5 refute value4. n8 distinct outputs tie64 defeating unique named maximizer.','qualification':'Conjecture5.2 separate multiplicity clause not refuted by n5. No all-n positive maximum theorem claimed.','remaining':'Actual journal body DOI10.1016/j.disc.2025.114834 and correction chronology unread; no full applicable prior subsumer established; current registry and substantive eligibility HOLD','reopen_trigger':'Lawful actual later body or exact-map relevant prior theorem/counterexample; no further sweep or formal investment now'}
 write('adjudications.json',adj);hyp=j(I/'hypothesis-queue.json')
 for q in hyp:
  if q['mathdb_id']==365437:q['status']='PARK_SOURCE_PRIOR_HOLD';q['review']=N+'/review.md';q['credit']=0
 write('hypothesis-queue.json',hyp)
 active=j(I/'active-breadth-reservations.json');assert len(active)==2
 for r in active:r['active_hypothesis_ids']=[]
 blocked=set(map(int,cov))|{i for r in active for i in r['ids']}|set(active[0]['protected_ids'])
 route=[json.loads(l) for l in (I/'routing-queue.jsonl').open()];assert len(route)==6000
 (P/'routing-queue.jsonl').write_bytes((I/'routing-queue.jsonl').read_bytes());rows=[r for r in route if r['mathdb_id'] not in blocked][:50];assert len(rows)==50
 res={'lane':'sol-mathdb-primary-qualified-breadth-r532','ids':[r['mathdb_id'] for r in rows],'coverage_baseline':4233,'protected_ids':active[0]['protected_ids'],'active_hypothesis_ids':[],'status':'reserved_not_reviewed'};active.append(res)
 allids={i for r in active for i in r['ids']};assert len(allids)==150
 for r in active:r['other_active_reservations']=sorted(allids-set(r['ids']))
 write('active-breadth-reservations.json',active);write('queue.json',rows);write('reserved-ids.json',res)
 (P/'DECISION.md').write_text('''# Root r531: stack-fiber family PARK

Retain r528's independent ordinary refutations of Zhao arXiv2410.17057v1 Conjectures5.2/4.19; PARK before further discovery investment. At n5 the second-largest distinct fiber has size5 rather than4; the separate predicted multiplicity8 at size4 is not refuted. At n8 alternative and named outputs tie64, so unique named maximization fails regardless of any larger fiber. This is one family, not two credits. Root did not replay mathematics.

Source full v1 textual body and applicable arguments read; literal top-to-bottom/vincular adjacency/greedy transitions independently checked. Actual journal body remains unread: DiscreteMath349(3),114834,DOI10.1016/j.disc.2025.114834 metadata reports online2025/issue2026,not exact correction chronology or conjecture survival. Consecutive-pattern papers concern different maps and provide no demonstrated full subsumption. No positive exclusion bridge or substantive/novelty clearance established. Reopen only on lawful actual later body or relevant exact-map prior; no further finite sweep,Lean,manuscript or access fishing now.

Preserve reviewer truncated displays,unrelated-record derivative timing and corrected source-root/catalogue lookup,plus producer failures. Integrity does not cure deviations or establish scientific acceptance. Coverage unchanged4,233;counts9additional/39total/next40. Sol r530 breadth continues;freed Sol slot resumes breadth r532 with50disjoint records. Claude r504 remains rate-limited/unreviewed reserved;no provider substitution/retry. Existing adjudications otherwise unchanged. Root only administrative/hash/assignment checks;no upstream verifier or math code execution.
''')
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and str(p.relative_to(P)) not in {'manifest.json','verification-receipt.json'}:
   b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'sha256':h(b),'size':len(b)})
 write('manifest.json',{'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':files})
def verify():
 cov=validate();assert j(P/'coverage-delta.json')==cov;active=j(P/'active-breadth-reservations.json');seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not set(map(str,ids))&set(cov) and not ids&set(r['protected_ids']);seen|=ids
 assert len(seen)==150
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 assert set(j(P/'reserved-ids.json')['ids'])=={r['mathdb_id'] for r in j(P/'queue.json')};assert (P/'routing-queue.jsonl').read_bytes()==(I/'routing-queue.jsonl').read_bytes()
 exact(P,j(P/'manifest.json'))
 try:check(P/'DECISION.md',{'size':0,'sha256':'0'*64})
 except AssertionError:pass
 else:raise AssertionError('negative accepted')
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','coverage_unchanged':4233,'child_payloads':len(j(F/N/'manifest.json')['files']),'child_flat_references':len(j(F/N/'flat-bindings.json')),'root_binding_pairs':len(j(P/'bindings.json')),'original_chunks':20,'frozen_inputs':8,'reservation_disjointness':True,'negative_rejection':True,'root_mathematical_replay':False,'counts':{'additional':9,'total':39,'next':40}};write('verification-receipt.json',r);print(json.dumps(r))
if '--build' in sys.argv:build();print('built')
else:verify()
