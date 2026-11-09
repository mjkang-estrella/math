import pathlib,json,hashlib,datetime,re,html,shutil
L=pathlib.Path(__file__).resolve().parent;B=L.parent.parent;R=B.parents[3]
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def w(n,o):(L/n).write_text(o if isinstance(o,str) else json.dumps(o,indent=2,ensure_ascii=False))
# Preserve the initial administrative basename collision as a failure record.
p=L/'administrative/bindings.json';shutil.copyfile(p,L/'administrative/initial-bindings.json')
admin=[]
for src,name in [(B/'AGENTS.md','batch-AGENTS.md'),(R/'AGENTS.md','ancestor-AGENTS.md'),(B/'ledger.json','ledger.json'),(B/'prior-campaign-context.json','prior-campaign-context.json'),(R/'sources/upstream.json','upstream.json')]:
 a=h(src);dst=L/'administrative'/name;shutil.copyfile(src,dst);assert a==h(src)==h(dst);admin.append(dict(original=str(src),snapshot=str(dst),sha256=a))
w('administrative/bindings.json',admin)
rows=[];chron=[]
for p in sorted((L/'frozen').glob('*.pdf')):
 b=json.loads((L/'bindings'/(p.stem+'.json')).read_text());assert h(p)==b['sha256']==h(pathlib.Path(b['original']))
 t=L/'texts'/(p.stem+'.txt');rows.append(dict(id=p.stem,url='https://arxiv.org/pdf/'+p.stem,primary=b['original'],frozen=str(p),sha256=h(p),bytes=p.stat().st_size,extracted_text_sha256=h(t)))
 q=L/'primary'/(p.stem+'-abs.html');s=html.unescape(re.sub('<[^>]+>',' ',q.read_text()));s=re.sub(r'\s+',' ',s)
 j=s.find('Submission history');chron.append(dict(id=p.stem,abs_url='https://arxiv.org/abs/'+p.stem,abs_sha256=h(q),submission_history=s[j:j+1800] if j>=0 else 'No parsed history; inspect retained HTML',pdf_titlepage=t.read_text()[:2100]))
w('primarybindings.json',rows);w('chronology.json',chron)
refs=json.loads((L/'history-bindings.json').read_text());drift=[]
for x in refs:
 p=pathlib.Path(x['path'])
 if not p.exists() or h(p)!=x['sha256']:drift.append(x['path'])
w('history-postcheck.json',{'bound':len(refs),'changed_or_missing':drift,'copy_policy':'immutable path+hash references; no recursive historical trees copied'})
p=L/'SCOUTING.md';s=p.read_text();s=s.replace('and containing0 is univalent','is univalent');p.write_text(s)
w('SUMMARY.md','''# r257 handback

Twelve distinct attributed source-question families screened across analysis, probability, prediction, geometry and special functions,2014–2026. Seventeen actual primary PDFs retained with hashes, version metadata and bounded live searches. No qualified ranked survivor and no discovery credit requested.

Sustained full-scope work on fGn predictor positivity,2209.02501 Conj(A), with the actual2024 follow-up and2026 asymptotic comparison: two routes yield exact obstructions, not a solution. The all-H covariance mixture cannot have finite lag-zero mass. An exact positive Toeplitz witness defeats the proposed positive-PACF induction even with decreasing positive log-convex covariances. See discovery.md and boundedchecks.json.

PROOF.md fully refutes Bosch's universal square-root Gamma-product HCM assertion, but explicitly excludes it as routine: the source density and classical half-integer Bessel evaluation already give the entire bridge. HOLD review; no newness claimed. Gaussian exchangeable rigidity and diagonal Hausdorff convexification were positively excluded using actual June2026 counterpart proofs.

Freshness remains bounded: denied routes were parked, no public-registry head obtained, historical/citing body gaps explicit. The initial unbound r254 report read and administrative basename collision are preserved in FAILURES.md. Root alone accepts/counts;9 additional/39 total/next40 unchanged. Solo, assigned lane only; no shared/git/public/browser/MathDB/Lean/manuscript actions.

finalmanifest.json excludes itself and verification-receipt.json. A separate guarded verifier checks the final bytes and every primary original/copy binding after writes.
''')
w('FAILURES.md','''# Failures and limitations

1. The initial native file inventory was excessively broad and truncated. It was used only to locate administration/guard and exposed no secret. Subsequent inventories and reads were bounded.
2. Before creating the lane freeze, the r254 SUMMARY/SCOUTING reports were read natively. This violated the requested pre-reading binding order for those reports. They were later hash-bound among876 reports, but that does not retroactively repair the first read. No r254 mathematical result is reused here; its retired coupon nomination was excluded as instructed.
3. Initial administrative snapshots used AGENTS.md for two ancestors, overwriting the batch copy with the ancestor copy. Initial binding records are preserved in administrative/initial-bindings.json. finalize.py repairs this with distinct batch-AGENTS.md and ancestor-AGENTS.md snapshots; no scientific source was affected.
4. init temporarily aggregated bound report text in history-index.json. This redundant aggregation was removed in a guarded compact invocation. Only immutable path/hash bindings and compact relevant hits remain; no historical evidence trees were copied.
5. The first searches were noisy and returned resolved2026 announcements. Those are not claimed as original fresh targets. Exact-author follow-up caught the full Gaussian rigidity proof before major further investment; actual proof body read and excluded. The initial idea that the target might remain open was abandoned.
6. fGn mixture route fails by divergent required lag-zero mass. Levinson route fails without an additional asymmetric ratio invariant. Exact obstruction witness is not fGn. No finite grid or asymptotic PACF law is promoted to a universal proof.
7. Gamma-product HCM counterexample is a complete routine formula adaptation, not a credited discovery. No infinite-divisibility/GGC conclusion follows from its failure of HCM.
8. Some automatic method-excerpts first matches are recalled statements rather than proofs. Do not infer full-paper audits from the file. Exact deeper reads and source gaps are described in SCOUTING/discovery. Historical original Qi2019,Kochar2009,Ruscheweyh2009,Dyn–Farkhi2004 and several precursor monographs were not retrieved; no false clearance is asserted.
9. Denied GitHub API/raw/codeload/diff/patch,ScienceDirect and Google challenge routes were not retried. No proxy,TLS-disable,browser or account bypass. No403/429/challenge occurred in the new successful arXiv requests. No current public-registry head obtained; stale history is not live clearance. Search indexing and complete citer coverage remain insufficient for novelty acceptance.
10. The handback does not achieve a new full source-question resolution eligible for credit. It provides breadth, sustained exact failed-route analysis, a routine exclusion proof and positive public exclusions. No acceptance request.
''')
w('progress.json',{'status':'SCOUT COMPLETE; SOLVING INCOMPLETE; NO QUALIFIED SURVIVOR','screened_families':12,'primary_pdf_count':len(rows),'ranked_survivors':[],'sustained_question':'2209.02501 Conjecture(A)','approaches':2,'ordinary_complete_excluded_proof':'1402.1059 Remark1(a), PROOF.md; EXCLUDE_ROUTINE/HOLD_REVIEW','counts':{'additional':9,'total':39,'next':40},'root_alone_counts':True,'history_drift':drift})
guard=B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
w('provenance.json',{'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane':str(L),'guard':str(guard),'guard_sha256':h(guard),'caps':{'AS_MiB':512,'group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'cap_raises':False},'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'retrieval':'guarded urllib HTTPS, bounded12MB responses and28sec timeout; arXiv only','source_freeze':'primary PDF saved+hashed, separate frozen copy hashed against original before extraction; originals/copies rechecked afterward and at finalization','administrative':'snapshot only, distinct ancestor filenames after documented repair','history':'876 immutable report bindings, compact exact-id/author/object alias hits; no recursive copies','novelty':'NOT CLEARED; no current registry head; no qualified new survivor','external_mutations':False})
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']:
  files.append(dict(path=str(p.relative_to(L)),sha256=h(p),bytes=p.stat().st_size))
w('finalmanifest.json',{'excludes':['finalmanifest.json','verification-receipt.json'],'files':files})
print(json.dumps({'manifest_files':len(files),'primary_pdf_bindings':len(rows),'history_drift':len(drift)}))
