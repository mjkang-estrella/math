import pathlib,json,hashlib,sys,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent;F=P/'frozen'
N494='claude-mathdb-banzhaf-source-prior-review-r494';N500='sol-mathdb-primary-qualified-breadth-r500';N502='sol-mathdb-linear-two-tree-prior-boundary-r502';BASE=F/'root-mathdb-linear-two-tree-review-intake-r501';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size {p}';assert h(b)==e['sha256'],f'hash {p}'
def write(name,o): (P/name).write_text(json.dumps(o,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
def exact(root,m):
 ex=set(m['excluded_exact_paths']);files=m['files'];assert len(files)==len({e['path'] for e in files})
 assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-ex=={e['path'] for e in files},f'file set {root}'
 for e in files:check(root/e['path'],e)
def inputs():
 refs=j(P/'bindings.json')
 for e in refs:
  for key in ['original','copy']:check(pathlib.Path(e[key]),e)
 for name in [N494,N500,N502]:
  m=j(F/name/'manifest.json');exact(F/name,m);exact(L/name,m)
 for name,filename in [(N500,'flat-bindings.json'),(N502,'flat-actual-bindings.json')]:
  for e in j(F/name/filename):check(pathlib.Path(e['path']),e)
 bn=j(F/N494/'bindings.json')
 for e in bn['inputs']:
  check(B/e['path_from_batch'],e)
  if 'original_path_from_batch' in e:check(B/e['original_path_from_batch'],e)
 for e in bn['fetched']:
  if e['retained']:check(F/N494/e['lane_path'],e);check(L/N494/e['lane_path'],e)
  else:assert not (F/N494/e['lane_path']).exists()
 receipt=(F/N494/'verification-receipt.txt').read_text();v=json.JSONDecoder().raw_decode(receipt[receipt.index('{'):])[0]
 assert v['integrity']=='PASS' and not v['errors'] and all(v['selftests'].values()) and 'verify_exit 0' in receipt
 r=j(F/N500/'final-receipt.json');assert r['exit_code']==0 and r['negative_test_rejected'] and json.loads(r['stdout'])['integrity']=='PASS'
 r=j(F/N502/'final-receipt.json');assert r['integrity']=='PASS' and len(r['mismatch_rejection_tests'])==5
 cm=j(F/'pi-mathdb-full-corpus-inventory-r301/manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:
  p=pathlib.Path(e['path']);check(p if p.is_absolute() else C/p,e)
 old=j(BASE/'coverage-delta.json');assert len(old)==3683
 ds=j(F/N500/'dispositions.json');assignment=j(F/'root-mathdb-abelianisation-retirement-intake-r499/reserved-ids.json')
 ids={d['ID'] for d in ds};assert len(ds)==len(ids)==50 and ids==set(assignment['ids']);assert not ids&set(map(int,old))
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(p,n,r)
 for d in ds:
  p,n,r=found[d['ID']];assert d['chunk']==str(p) and d['line']==n and d['literal']==r['statement']
  assert d['statement_utf8_sha256']==h(r['statement'].encode());assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert d['accepted_credit']==0
 assert j(F/N500/'proposals.json')==[]
 return old,ds,len(refs)
def build():
 old,ds,_=inputs()
 for d in ds:
  old[str(d['ID'])]={'source_lane':N500,'disposition':d['disposition'],'evidence_levels_reported':d['evidence_levels'],'statement_utf8_sha256':d['statement_utf8_sha256'],'canonical_record_sha256':d['canonical_record_sha256'],'accepted_credit':0,'prior_cleared':False,'root_scope':'literal/disjointness/hash reconciliation; no scientific upgrade'}
 write('coverage-delta.json',old)
 adj=j(BASE/'adjudications.json');adj['338290']={'disposition':'RETIRE_PRIOR_DEFEATED','credit':0,'review':N494+'/review.md','source':'Gafni–Lavi–Tennenholtz, arXiv:2108.09216v1, Theorem 4.1, Example 4.1 and Appendix C; JAIR 72 (2021) 99–135 DOI 10.1613/jair.1.13136','bridge':'One big player makes big-player weight share equal maximum weight/total; their unbounded absolute and normalized ratios exceed 2. Strict-majority restriction also fails by duality.','evidence_limit':'Actual arXiv proof body read by independent reviewer; typeset JAIR/IJCAI bodies not read; no explicit named refutation of Conjecture 3.8 established.','current_registry_cleared':False}
 adj['337963']={'disposition':'PARK_SOURCE_PRIOR_SUBSTANTIVE_HOLD','credit':0,'reviews':[N502,'sol-mathdb-linear-two-tree-source-prior-review-r498'],'math_status':'Reported independent ordinary PASS; not root replayed','remaining':'2020 arbitrary-bend and reported 2026 monotonicity bodies unavailable; full structural subsumption and current registry unresolved'}
 write('adjudications.json',adj)
 write('hypothesis-queue.json',[{'mathdb_id':int(k),'status':v['disposition'],'credit':0} for k,v in adj.items()])
 excluded={337963,338290,339564,372627,372628,368940,404067,364119}
 route=[json.loads(line) for line in (F/'root-mathdb-breadth-intake-r415/routing-queue.jsonl').open()]
 available=[r for r in route if str(r['mathdb_id']) not in old and r['mathdb_id'] not in excluded]
 assert len(available)>=150,('routing expansion needed',len(available))
 lanes=['claude-mathdb-primary-qualified-breadth-r504','sol-mathdb-primary-qualified-breadth-r506','sol-mathdb-primary-qualified-breadth-r508'];allids=[r['mathdb_id'] for r in available[:150]];assert len(set(allids))==150
 reservations=[]
 for i,name in enumerate(lanes):
  rows=available[i*50:(i+1)*50];ids=[r['mathdb_id'] for r in rows];stem=name.rsplit('-',1)[-1]
  write('queue-'+stem+'.json',rows)
  res={'lane':name,'ids':ids,'other_active_reservations':[x for x in allids if x not in ids],'active_hypothesis_ids':[],'protected_ids':sorted(excluded),'status':'reserved_not_reviewed','coverage_baseline':3733}
  write('reserved-ids-'+stem+'.json',res);reservations.append(res)
 write('active-breadth-reservations.json',reservations)
 write('coverage-summary.json',{'reported_literal_reviews':3733,'new_literal_reviews':50,'known_ids':95675,'retrieved_records':87990,'missing_records':7685,'new_reservations':150,'counts':{'additional':9,'total':39,'next':40},'full_technical_corpus_review':False})
 (P/'DECISION.md').write_text('''# Root reconciliation and routing — r503

Retire MathDB338290 from discovery investment as defeated by the published Gafni–Lavi–Tennenholtz result. Adopt the independent r494 applicability bridge, not a claim that the named conjecture was explicitly refuted in print. The read proof body is arXiv:2108.09216v1; correspondence to JAIR 72 (2021) rests on DOI/metadata, not a typeset-body comparison. Both absolute and normalized readings fail. Minimality is unnecessary and not adopted. No credit.

Park MathDB337963 after r502. Source Definition 45 is qualified; preserve r498's ordinary mathematics report. Neither closest later body was obtained. No published full-class subsumer has been established, and substantive novelty is not cleared. No further source fishing, formalization or manuscript investment now.

Reconcile the fifty r500 literal reviews with exact corpus text, canonical record hashes and disjointness. Coverage becomes 3,733 reported literal reviews, not 3,733 complete proof or novelty audits. Selected source readings and unresolved successor/dependency obligations remain as reported. Source-known retirements are not silently upgraded to independent proof audits. No qualified briefs survive this batch.

Reserve 150 fresh routing records in three mutually disjoint fifty-record batches: Claude r504 and Sol r506/r508. All previous delegates have completed. Root remains orchestrator; hypothesis work must be separately delegated. Existing exclusions and protected candidates remain protected. Whole-corpus review is incomplete: 95,675 known IDs, 87,990 retrieved records, 7,685 missing at the inventory checkpoint.

Preserve failures: r494 pre-freeze administrative display, one already-scripted S2 request after 429, deleted bytecode cache and tool timeout within guard; r500 overbroad historical display/timing and truncated exploratory windows; r502 helper-text binding timing and inherited r498 deviation. Root's first administrative cat named a nonexistent cwd AGENTS.md (exit 1); both existing mandatory instructions were read. Integrity does not erase deviations or establish mathematics/novelty.

Counts unchanged: 9 additional / 39 total / next 40. No upstream verifier or mathematical checker executed by root; root checks only files, receipts, assignment and corpus reconciliation. No MathDB or other network requests by root.
''')
 seal()
def seal():
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and p.name not in [] and str(p.relative_to(P)) not in {'manifest.json','verification-receipt.json'}:
   b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'sha256':h(b),'size':len(b)})
 write('manifest.json',{'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':files})
def verify():
 old,ds,nrefs=inputs();cov=j(P/'coverage-delta.json');assert len(cov)==3733 and set(cov)==set(old)|{str(d['ID']) for d in ds}
 for k,v in old.items():assert cov[k]==v
 rs=j(P/'active-breadth-reservations.json');ids=[]
 for r in rs:
  assert len(r['ids'])==len(set(r['ids']))==50 and not set(map(str,r['ids']))&set(cov)
  assert not set(r['ids'])&set(r['protected_ids']);ids+=r['ids']
 assert len(set(ids))==150
 for r in rs:assert set(r['other_active_reservations'])==set(ids)-set(r['ids'])
 exact(P,j(P/'manifest.json'))
 sample={'size':1,'sha256':'0'*64}
 try:check(P/'DECISION.md',sample)
 except AssertionError:rejected=True
 else:raise AssertionError('negative control accepted')
 receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','root_original_copy_bindings':nrefs,'child_payload_counts':{name:len(j(F/name/'manifest.json')['files']) for name in [N494,N500,N502]},'corpus_chunks':20,'inventory_frozen_inputs':8,'coverage':3733,'new_disjoint_reservations':150,'negative_control_rejected':rejected,'scientific_acceptance':False,'counts':{'additional':9,'total':39,'next':40}}
 write('verification-receipt.json',receipt);print(json.dumps(receipt))
if __name__=='__main__':
 if '--build' in sys.argv:build();print('built and sealed')
 else:verify()
