import pathlib,json,hashlib,re
L=pathlib.Path(__file__).resolve().parents[1]
log=L/'logs'
closure=(log/'closure.txt').read_text().splitlines()
built=[p.stem.removeprefix('build-') for p in log.glob('build-StackSort*.log')]
for p in log.glob('build-StackSort*.log'):assert p.read_text().rstrip().endswith('exit 0'),p
for name in ['checker-StackSortFinal6.log','examples.log','independent.log']:
    assert (log/name).read_text().rstrip().endswith('exit 0'),name
assert set(closure)<=set(built)
ax=(log/'build-StackSortFinal6.log').read_text()
names=['mathdb_345545','limit_ge','nonvacuity','subsequence_companion','mathdb_345545_max','max_companion']
for n in names:
    m=re.search(r"'StackSort.Round6\."+n+r"' depends on axioms: \[(.*?)\]",ax,re.S)
    assert m,n
    assert set(x.strip() for x in m.group(1).split(','))=={'propext','Classical.choice','Quot.sound'},n
rss=[]
for p in log.glob('*.log'):
    rss += [int(x) for x in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',p.read_text())]
assert (L/'hashes/before.sha256').read_bytes()==(L/'hashes/after.sha256').read_bytes()
inputs=[]
for line in (L/'hashes/before.sha256').read_text().splitlines():
    sha,path=line.split('  ',1);inputs.append({'path':path,'sha256_before':sha,'sha256_after':sha})
report={
'review_type':'INDEPENDENT FORMAL-FIDELITY REVIEW, NOT ACCEPTANCE',
'mathdb_id':345545,'self_accepted':False,'credit':0,'root_decides':True,
'archive_sha256':'9b734e2fe521651fd33bbf92bdf05f1b542a6aeb82f90d2cd1e13399d6cf5c2f',
'gates':{
'A':{'verdict':'PASS','summary':'Literal maximum-split map on permutation words; exact collision count and Definition 1.1 bridges; correct real rpow, interval and quantifiers; explicit arbitrarily large witnesses; maximum reading separate.','references':['StackSortBasic.lean:14','StackSortBasic.lean:32','StackSortBasic.lean:34','StackSortBasic.lean:37','StackSortBasic.lean:46','StackSortBasic.lean:52','StackSortMap.lean:53','StackSortMap.lean:56','StackSortEquivariance.lean:13','StackSortFinal6.lean:21','StackSortFinal6.lean:26','StackSortAnalysis.lean:59']},
'B':{'verdict':'PASS','summary':'Every ordinary Prop is supplied at the final endpoints. Literal finite bijections close both last counting obligations. Finite seed clipping is sound and its scope is explicit.','references':['StackSortFinal6.lean:6','StackSortFinal6.lean:14','StackSortDoubling3.lean:3','StackSortRootSplit3.lean:86','StackSortInj2Lower.lean:45','StackSortInj2Linkage.lean:138','StackSortSeeds2Final.lean:41','StackSortCut5Count.lean:31','StackSortTagged6.lean:80','StackSortTaggedCount6.lean:34','StackSortFixedCount6.lean:107','StackSortAnalysis.lean:25']},
'C':{'verdict':'PASS','summary':'Own recursive/iterative Python enumeration through 7 matches literal seeds and frozen table; independent G130/certificate arithmetic agrees. Own strict Lean examples kernel-reduce P3/P4 and certificate; derive P5/P6 through proved recursion.','evidence':['scripts/independent.py','build/src/ReviewExamples.lean','logs/independent.log','logs/examples.log','logs/independent-results.json'],'direct_P5_P6_retried':False,'direct_P5_P6_limit_is_proof_gap':False},
'D':{'verdict':'PASS','scope':'Bounded independent formal check; not root decisive replay','strict_proof_modules_built':len(built),'endpoint_local_import_closure_modules':len(closure),'all_endpoint_import_closure_built':True,'diagnostic_audit_utilities_built':False,'leanchecker_modules':['StackSortFinal6'],'endpoint_axioms':{n:['propext','Classical.choice','Quot.sound'] for n in names},'source_scan_modules':92,'source_scan_forbidden_tokens':[],'evidence':['scripts/build.sh','scripts/run.sh','logs/build-progress.log','logs/build-StackSortFinal6.log','logs/checker-StackSortFinal6.log','logs/closure.txt']},
'E':{'verdict':'QUALIFIED_PASS','summary':'Formal statement correspondence is ready; manuscript integration and root replay remain. No completed manuscript or fresh prior-art search reviewed.','required_items':['State refutation, every-possible-limit bound at least 1.73, frequent strict exceedance, explicit dyadic indices; attribute existence to source Theorem 2.5.','Present exact finite recursion, multiplicities, shuffle coefficients, seed table, lower recursion and integer certificate; distinguish finite formal scope from an unrestricted polynomial-time algorithm.','Cover both readings and give no credit for the defective maximum-fibre paraphrase.','Correct version history: v3/v4 Conjecture 4.4 and EJC Conjecture 23 versus v1/v2 (1.6,1.8) remark.','Disclose that exact seeds through 13 plus RootSplit and doubling already suffice; do not claim new recursion is essential to bare refutation.','Describe audits, bounded checks, and direct P5/P6 reduction limits accurately.','Describe frozen-source and prior-art access limits; no exhaustive novelty claim.']}
},
'required_lean_source_fixes':[],
'required_before_acceptance':['Root decisive fresh replay','Manuscript integration of gate E items','Root significance, novelty and acceptance adjudication'],
'inputs':inputs,'hashes_unchanged':True,
'resources':{'watchdog_RSS_KiB':6291456,'peak_recorded_RSS_KiB':max(rss),'cpu_seconds_per_call':120,'wall_seconds_per_call':140,'cpus':[0,1],'lean_flags':['-j1','-M3500','-DwarningAsError=true'],'MALLOC_ARENA_MAX':2,'one_heavy_process_at_a_time':True,'TMPDIR_and_cache_lane_local':True},
'no_child_agents':True,'no_git':True,'no_network':True,'no_external_messages':True,'no_publication_or_upload':True,'no_browser_tabs':True,'background_jobs_remaining':False,
'limitations':['Only StackSortFinal6 passed as explicit leanchecker target; dependencies were strictly compiled, not each separately checker-invoked in this review.','No review-time transitive declaration metadata dump; endpoint axioms and all-source scan performed. Existing packet metadata audit remains separately reported implementation evidence.','No independently repeated direct P5 or P6 kernel enumeration under unchanged resource limits.','No new prior-art or other-version downloads; rely on frozen review evidence for those histories.']}
(L/'review.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print('final report validated; strict modules',len(built),'closure',len(closure),'peak RSS',max(rss),'KiB; all inputs unchanged')
text=(L/'REVIEW.md').read_text()
text=text.replace('## C. Independent semantic sanity — pending run results','## C. Independent semantic sanity — PASS')
text=text.replace('## D. Bounded formal spot check — pending run results','## D. Bounded formal spot check — PASS (bounded scope)')
text=text.replace('The review\'s own `scripts/independent.py`', 'Completed results: P0 through P7 are 1, 1, 4, 26, 224, 2356, 29064, 411172; both algorithms agree for every permutation enumerated. All 20 seed literals match the frozen table. The independently computed G130 equals the packet literal and the certificate inequality is strict. The review Lean examples pass strict compilation, including direct kernel reductions P0 through P4 and certificate130, and recursion-derived P5 through P7. Full logs: `logs/independent.log`, `logs/examples.log`.\n\nThe review\'s own `scripts/independent.py`')
text=text.replace('All Lean, leanchecker and Python calls use',f'Completed: all {len(built)} proof modules, exactly the {len(closure)}-module local import closure of StackSortFinal6, passed strict compilation from the extracted sources. The explicit-module endpoint checker exited 0. All six final endpoints, and all six intermediate round 6 bridges printed in the endpoint module, depend only on propext, Classical.choice and Quot.sound (`logs/build-StackSortFinal6.log`). The comment/string-aware rescan of all 92 archived modules found none of sorry, admit, axiom, unsafe, partial, native_decide, ofReduceBool, implemented_by or extern. Every archived Lean source remains byte-identical. Peak recorded completed-call RSS was {max(rss):,} KiB, below the cap.\n\nAll Lean, leanchecker and Python calls use')
text += '''

## Evidence integrity, run history and limits

All 20 required input files were SHA-256 bound before inspection and after the checks; `hashes/before.sha256` and `hashes/after.sha256` are byte-identical. `review.json` embeds every before/after digest and absolute input path. `hashes/inputs.list` defines the input set. Archive sources were also compared byte for byte against the zip by the independent script. `logs/declaration-lines.txt` records source locations.

The first build invocation ended with signal 143 during StackSortMaximum4, without a reported Lean error; the cause is unknown. The incomplete wrapper log and `logs/interrupted-StackSortMaximum4.log` were retained. A resumed build reused only modules already compiled in this lane and rebuilt that interrupted module successfully. This is a resumed bounded rebuild, not an uninterrupted replay. The review examples first failed because the reviewer omitted unfolding `roots` in a `simpa only` frequency check; `logs/examples-attempt1.log` retains that diagnostic. Adding `roots` to that simplification fixed the review-only example. No packet source was changed.

The endpoint checker was the only explicit checker target; this review does not claim that leanchecker was separately invoked on all 84 dependencies. It did not repeat the implementation's environment-wide metadata audit or current prior-art search. The source scan and endpoint transitive axiom prints were independently performed here. The package location and revision are those prescribed in the brief; no git operation was used to re-establish the package checkout revision.

All completed heavy calls ran serially under the resource wrapper. No review process or background job remains at handback. Root's decisive fresh replay and the manuscript integration items remain outstanding; there is no self-acceptance.
'''
(L/'REVIEW.md').write_text(text)
report['run_history']={'initial_build_exit':143,'initial_build_interrupted_at':'StackSortMaximum4','cause':'unknown; no Lean diagnostic reported','resumed_using_only_lane_local_successful_oleans':True,'review_example_first_attempt':'frequency check needed explicit unfolding of roots; fixed in review-only file','packet_sources_modified':False}
(L/'review.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
