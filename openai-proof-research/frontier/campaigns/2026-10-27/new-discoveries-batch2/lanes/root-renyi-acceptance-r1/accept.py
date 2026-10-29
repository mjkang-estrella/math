import datetime,hashlib,json,pathlib,shutil,subprocess,sys
P=pathlib.Path(__file__).resolve().parent
B=P.parents[1]; lanes=P.parent
S=lanes/'sol-renyi-threshold-manuscript-packet-r1'
R=lanes/'root-renyi-final-review-freeze-r1'
F=lanes/'sol-renyi-threshold-full-final-review-r1'
D=lanes/'sol-renyi-final-delta-closure-r4'
FF=lanes/'sol-factorial-product-full-final-review-r1'
EX=lanes/'root-factorial-final-exclusion-r1'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
def load(p):return json.loads(p.read_text())
def dump(p,j):p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
def frozen(p):
 j=load(p)
 for k,v in j['files'].items():assert sha(pathlib.Path(j['root'])/k)==v,k
 return len(j['files'])
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
ledger=load(B/'ledger.json')
assert ledger['accepted_count']==8 and ledger['total_accepted_count']==38
assert [x['number'] for x in ledger['accepted']]==list(range(31,39))
first=B.parent.parent/'2026-10-26/new-discoveries/ledger.json'
firstsha='4b2b8556921bb11448e76e0653060ab89d9b2107f3be0338c238ba66038bc385'
assert sha(first)==firstsha
counts={'renyi_candidate':frozen(R/'freeze.json'),'renyi_review':frozen(lanes/'root-renyi-final-review-adoption-r1/review-freeze.json'),'factorial_candidate':frozen(lanes/'root-factorial-final-review-freeze-r1/freeze.json')}
for k,v in load(FF/'final-manifest.json').items():assert sha(FF/k)==v,k
counts['factorial_review_manifest']=len(load(FF/'final-manifest.json'))
check=subprocess.run([sys.executable,str(D/'check.py')],env={**__import__('os').environ,'PYTHONDONTWRITEBYTECODE':'1'},capture_output=True,text=True,check=True)
(P/'registry-check.log').write_text(check.stdout+check.stderr)
coverage=json.loads(check.stdout)
assert coverage['result']=='PASS' and coverage['unique_mainline_changed_paths']==538
rr=load(R/'rebuild/replay/replay-receipt.json')
assert rr['full_target_proved'] and rr['source_claim_pass'] and rr['initial_own_prebuilt_artifacts']==0
assert len(rr['modules'])==11 and rr['declaration_count']==len(rr['declarations'])==104
assert len({r['name'] for r in rr['declarations']})==104
allowed={'propext','Classical.choice','Quot.sound'}
for r in rr['declarations']:
 assert r['actual_type'] and r['origin'] in rr['modules']
 assert set(r['axioms'])<=allowed and not any(r[k] for k in ('unsafe','partial','axiom'))
assert {'Renyi.every_order_counterexample','Renyi.not_source_threshold'}<={r['name'] for r in rr['declarations']}
assert all(s['exit']==0 and s['kill'] is None for s in rr['steps'])
rb=load(R/'ROOT-REBUILD.json')
assert rb['root_fresh_execution'] and rb['root_read_all_four_pages'] and rb['byte_identical_pdf_and_zip']
assert sha(R/'rebuild/replay/replay-receipt.json')==rb['replay_receipt_sha256']
assert sha(S/'paper.pdf')==rb['paper_sha256']=='44506a1d71a405c7a8bedab38ce51d7ed4ae08fd9a22d2013d3fab52a90bbe83'
assert sha(S/'packet.zip')==rb['packet_sha256']=='8e334cd5702319a79e9001e179ae8211b818100a4f1db4b440a6f93be3a9d555'
C=B/'candidates/renyi-threshold';C.mkdir(exist_ok=True)
shutil.copy2(S/'paper.pdf',C/'paper.pdf')
shutil.copy2(S/'packet.zip',B/'candidate-packets/subunit-renyi-threshold-refutation.zip')
shutil.copy2(S/'packet/build_paper.py',C/'build_paper.py')
shutil.copy2(R/'rebuild/replay/replay-receipt.json',P/'replay-receipt.json')
shutil.copy2(R/'ROOT-REBUILD.json',P/'root-rebuild-receipt.json')
shutil.copy2(R/'rebuild/receipt.json',P/'verification-receipt.json')
entry={
 'number':39,'status':'ACCEPT: full proposed subunit threshold refuted; all mathematical gates PASS with bounded prior-art and procedural qualifications',
 'discovery_count_credit':1,'title':'Failure of the exponential Rényi-increment threshold below one',
 'source_target':'Fu–Li, A reverse entropy power inequality for iid log-concave random variables, arXiv:2510.09206v3, printed p2 unnumbered paragraph after (1.2)',
 'source_url':'https://arxiv.org/abs/2510.09206v3',
 'scope':'For every real 0<p<1 there exists a finite normalized truncated exponential whose iid positive-sum Rényi entropy increment strictly exceeds the exponential increment. Consequently no threshold p0 in (0,1) has the proposed exponential-maximizer property above p0.',
 'formal_scope':'Literal real density/convolution/moment/entropy endpoints, with all admissibility conditions proved. Refutes a necessary density-level source consequence. Independent-copy realization and scale invariance are ordinary source-translation arguments, not additional Lean endpoints.',
 'formal_modules':11,'formal_declarations':104,'allowed_axioms':sorted(allowed),'all_actual_unsafe_partial_axiom_flags_false':True,
 'endpoint':'Renyi.every_order_counterexample','source_refutation':'Renyi.not_source_threshold : ¬ Renyi.SourceThresholdConsequence',
 'packet':'candidate-packets/subunit-renyi-threshold-refutation.zip','packet_sha256':sha(S/'packet.zip'),
 'paper':'candidates/renyi-threshold/paper.pdf','paper_sha256':sha(S/'paper.pdf'),
 'manifest_sha256':sha(S/'packet/manifest.json'),'receipt_sha256':sha(P/'replay-receipt.json'),
 'final_extracted_receipt':'lanes/root-renyi-acceptance-r1/replay-receipt.json','parent_decision':'lanes/root-renyi-acceptance-r1/ACCEPTANCE.md',
 'independent_reviews':['lanes/sol-renyi-threshold-preliminary-review-r1/review.md','lanes/sol-renyi-threshold-current-prior-review-r2/review.md','lanes/sol-renyi-registry-gap-closure-r3/review.md','lanes/sol-renyi-threshold-full-final-review-r1/review.md','lanes/sol-renyi-final-delta-closure-r4/review.md'],
 'substantive_adjudication':'Elementary DCT and a familiar family remain the strongest objection. Inspected difference, Shannon, min-entropy and localization bodies supply no complete positive-sum changing-input quotient bridge. Scoped independent substantive PASS adopted; no separate credit for tools or formalization.',
 'novelty_limit':'Bounded primary-body and selective baseline screens; prior capped intervals and final 0d4df45→d254db mainline delta closed. 538 paths,525 reconstructed added bodies,13 immutable modified bodies. Not all transient side-branch states or worldwide literature; 51 historical source-context mismatches with recovered exact atoms remain disclosed.',
 'registry_evidence':'lanes/sol-renyi-final-delta-closure-r4/exactcoverage.json',
 'one_family':'One threshold refutation; every-order strengthening, DCT mechanism and all formal helpers uncredited separately. No Shannon p=1, actual optimizer, cube or uniform-cutoff result claimed.',
 'resource_limit':'Prescribed helper and serial Lean caps; RSS sampled. Historical PDF-authoring Node marker failure and inherited failed checks preserved. No claim of full authoring-skill compliance.',
 'postreview_manuscript_change':'None. Reviewed PDF/ZIP retained byte-identically including historical pending/credit-zero prose; dated acceptance sidecar supersedes draft status.',
 'first_batch_ledger_sha256_preserved':firstsha,'date':'2026-10-29','accepted_at_utc':now,
 'external_actions_performed':False,'path':'candidates/renyi-threshold','acceptance':'candidates/renyi-threshold/acceptance.json'}
decision={**entry,'frozen_counts':counts,'final_review_sha256':sha(F/'review.md'),'delta_review_sha256':sha(D/'review.md'),'root_coverage_checker':coverage,
 'root_review_limit':'Previously read mathematical sources and four renders; prior fresh root replay bound to unchanged bytes. This turn reread Endpoint and reviews, machine-checked all104 records and coverage. Oversized receipt display was truncated; no claim of reading every expanded type in that display.'}
dump(P/'ACCEPTANCE.json',decision);dump(C/'acceptance.json',decision)
shutil.copy2(P/'ACCEPTANCE.md',C/'ACCEPTANCE.md')
ex={'id':'distinct-factorial-product','status':'EXCLUDE_ROUTINE_CLASSICAL_ADAPTATION','discovery_count_credit':0,
 'reason':'Complete weighted concentration-box proof with almost-full smooth restriction and elementary two-scale factorial valuation estimates yields a distinct-support collision; final review reverses provisional substantive PASS. No prior exact printed collision asserted.',
 'decision':'lanes/root-factorial-final-exclusion-r1/DECISION.md','final_review':'lanes/sol-factorial-product-full-final-review-r1/review.md','formal_math_manuscript':'PASS retained;31 declarations and portable replay; no discovery credit','novelty':'CLEAR_BOUNDED, not worldwide'}
dump(EX/'EXCLUSION.json',{**ex,'utc':now,'review_sha256':sha(FF/'review.md'),'review_provenance_sha256':sha(FF/'provenance.json'),'candidate_frozen_paths':counts['factorial_candidate'],'review_manifest_paths':counts['factorial_review_manifest'],'supersedes':'Provisional substantive PASS only; frozen proof and historical review text unchanged.'})
assert not any(x.get('id')==ex['id'] for x in ledger['excluded'])
ledger['excluded'].append(ex);ledger['accepted'].append(entry)
ledger.update(accepted_count=9,total_accepted_count=39,next_global_outcome_number=40)
dump(B/'ledger.json',ledger)
nexttext=(B/'NEXT.md').read_text()
intro='''Outcome39 ACCEPTED: full subunit Rényi threshold refutation. For each real0<p<1,
a normalized truncated exponential beats the exponential iid positive-sum entropy
increment. Root and independent final replay11modules/104actual declarations,
four-page PDF and deterministic ZIP pass. Dedicated closure removes fixed
0d4df45→d254db cap:9steps/28commits/538paths. Bounded semantic/priority and
failed authoring-marker qualifications retained. Reviewed draft bytes unchanged;
acceptance sidecar supersedes pending prose. See root-renyi-acceptance-r1.

Factorial final review adopted SUBSTANTIVE FAIL: complete classical concentration
box/two-scale valuation bridge reaches exact distinct-support conclusion. Earlier
provisional PASS superseded; source/math/31declaration portable replay/paper remain
valid zero-credit artifacts. See root-factorial-final-exclusion-r1/DECISION.md.

Accepted9/30 additional,39/60 total; next40. Three active Sol high/default:
fresh research r119 (finite/arithmetic),r120 (analytic/geometric),r121
(structural/algebraic). All other pending wording below is historical.

'''
nexttext=nexttext.replace('# Current continuation — 29 October 2026\n','# Current continuation — 29 October 2026\n\n'+intro,1)
(B/'NEXT.md').write_text(nexttext)
results=(B/'RESULTS.md').read_text().replace('**8/30**','**9/30**').replace('**38/60**','**39/60**')
results=results.replace('\nEach acceptance has','\n|39|Every subunit Rényi order admits a truncated-exponential counterexample to the proposed exponential threshold|11 mathematical modules,104 declarations; root and independent extracted replay|[paper](candidates/renyi-threshold/paper.pdf), [decision](lanes/root-renyi-acceptance-r1/ACCEPTANCE.md)|\n\nEach acceptance has')
# Remove legacy blank separators inside the existing single result table.
results=results.replace('|\n\n|','|\n|')
(B/'RESULTS.md').write_text(results)
assert sha(first)==firstsha
assert sha(C/'paper.pdf')==entry['paper_sha256'] and sha(B/entry['packet'])==entry['packet_sha256']
dump(P/'INTEGRITY.json',{'utc':now,'counts':[9,39],'frozen':counts,'packet_sha256':entry['packet_sha256'],'paper_sha256':entry['paper_sha256'],'first_ledger_sha256':sha(first),'coverage':coverage,'status':'PASS'})
print(json.dumps({'accepted':39,'excluded':'distinct-factorial-product','counts':[9,39],'frozen':counts}))
