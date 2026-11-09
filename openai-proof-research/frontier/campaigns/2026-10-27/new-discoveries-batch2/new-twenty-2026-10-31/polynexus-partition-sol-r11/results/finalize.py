from pathlib import Path
import sys,subprocess,json,hashlib,re,os
lane=Path.cwd()
def write(p,s):subprocess.run([sys.executable,'-I','-B','write_lane.py',p],input=s,text=True,check=True)
def put(p,obj):write(p,json.dumps(obj,indent=2,sort_keys=True)+'\n')
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
rs=[(p,json.loads(p.read_text())) for p in sorted(Path('receipt').glob('*.json'))]
by={r['label']:(p,r) for p,r in rs}
mods=json.loads(Path('cleanroom/setup.json').read_text())['modules']
for m in mods:
 for label in ['clean_'+m,'cleanchecker_'+m]:assert by[label][1]['exit']==0,label
 assert digest(Path('src')/(m+'.lean'))==digest(Path('cleanroom/src')/(m+'.lean'))
all_decl=set();full_decl=set();audit_records=[]
for i in range(16):
 p,r=by['full_audit_'+str(i)];assert r['exit']==0,(p,r['exit'])
 s=Path(r['log']).read_text()
 assert '⋯' not in s and '…' not in s and 'UNSAFE true' not in s
 assert 'ROOT_COUNT 282 CLOSURE_COUNT 7003 AXIOMS [Quot.sound, Classical.choice, propext]' in s
 decl=set(re.findall(r'^DECL (\S+) ORIGIN ',s,re.M))
 full=set(re.findall(r'^FULL_DECL (\S+)$',s,re.M))
 assert len(decl)==7003
 assert not full_decl.intersection(full)
 all_decl.update(decl);full_decl.update(full)
 audit_records.append({'shard':i,'receipt':str(p),'exit':r['exit'],'full_declarations':len(full),'log_bytes':Path(r['log']).stat().st_size,'abbreviations':0})
assert full_decl==all_decl and len(full_decl)==7003
for label in ['negative_endpoint','negative_coupling']:
 assert by[label][1]['exit']==1
 assert 'error:' in Path(by[label][1]['log']).read_text()
assert json.loads(Path('frozen-after.json').read_text())['mismatches']==[]
put('results/deep-audit.json',{'roots':282,'closure':7003,'all_declarations_have_unabridged_types_and_available_opaque_bodies':True,'body_output':'disjoint exhaustive hash partitions, pretty printing maxSteps 1e9; zero abbreviation symbols','origins_and_safety_checked_for_full_closure':True,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'shards':audit_records,'failed_raw_attempt_preserved':str(by['audit_Raw'][0]),'pretty_abbreviated_development_audit_not_full_body_evidence':str(by['audit_Deep'][0])})
put('results/final-source-freeze.json',{str(Path('src')/(m+'.lean')):digest(Path('src')/(m+'.lean')) for m in mods})
results={'mathdb_id':352496,'implementation':'literal endpoint and source membership bridge proved','endpoint':'polynexus_literal','source_set_bridge':'PNZ_source','n1':'polynexus_one','production_modules':mods,'clean_compile_passes':12,'clean_checker_passes':12,'deep_audit':'results/deep-audit.json','negative_controls':{k:{'receipt':str(by[k][0]),'exit':by[k][1]['exit']} for k in ['negative_endpoint','negative_coupling']},'failures_preserved':[{'receipt':str(p),'label':r['label'],'exit':r['exit']} for p,r in rs if r['exit']!=0],'setup':'cleanroom/setup.json','setup_receipt':str(by['clean-setup'][0]),'frozen_before':'frozen-before.json','frozen_after':'frozen-after.json','accepted_count_unchanged':'52/60','credit':0,'review':'independent formal/manuscript and novelty/significance/root acceptance remain separate','evaluation_route':'certified finite gap convolution, evaluated by two finite induction identities; optional three-shift binomial expression not separately implemented','receipts':[str(p) for p,r in rs]}
put('results/keyed-results.json',results)
summary='''# Implementation handoff — MathDB 352496

The full literal integer endpoint is proved in src/PolynexusLiteral.lean (`polynexus_literal`), together with the exact signed-source operand-set equivalence `PNZ_source`, printed min/max legality equivalence, rational formula and n=1 theorem. The first production edit repaired the latest Partition compile failure and passed strict checking before any API lookup.

The implementation adds actual zero-pair gap bijections, disjoint length fibers, and a finite triangular-gap convolution. It evaluates that convolution by two induction/telescoping polynomial identities, replacing the optional formal-series/three-shift-binomial route. No answer-defined proxy, numerical experiment, external mathematics program or enumeration was used.

All 12 production modules compile fresh, all 12 kernel checker invocations pass. Setup was recorded with an empty build before compiling, and clean LEAN_PATH contains only own fresh build plus upstream libraries. No foreign project olean paths survive in clean receipts. Production sources equal the extracted sources exactly; final-source-freeze.json binds the review inputs.

Deep audit: 282 module-origin-selected production declarations (including generated/private names), 7,003 transitive declarations, actual types and opaque bodies. All safety/origin/axiom checks pass, only propext/Classical.choice/Quot.sound. Sixteen disjoint hash partitions provide unabridged types/bodies of the entire closure, checked for exhaustive coverage and zero abbreviation markers. The initially abbreviated audit and a CPU-limited raw-node serialization attempt are preserved as nonfinal evidence. Resource caps/runner were not modified. The raw-node attempt exited -9 at the 120 CPU cap; the final diagnostic-driven fix partitions body output, with every shard still checking the whole dependency closure.

Both meaningful negative controls failed as intended: changing the cubic endpoint sign gives a type mismatch; the old rectangle-style off-diagonal entry assertion reduces to False. Failure logs/receipts are preserved.

Manifest includes all own sources, extracted sources/oleans, frozen inputs, outputs, completed receipt JSONs and logs. Named terminal self-exclusions prevent circular hashing. Frozen-after verifies all 71 paths unchanged.

Independent source-aware formal review and manuscript review remain separate; novelty/significance and root acceptance are not claimed. Credit zero; accepted count 52/60 unchanged. No children, network, git, account, publication, foreign-lane bodies or dependency writes.

Startup reporting: the supplied directory has TASK.txt, not FULLTASK.txt. Bootstrap printed/read the complete TASK and AGENTS chain. Two initial guessed runner filenames did not exist; an own-directory inventory located runner.py. Those failed invocations executed no reader/writer. The runner implementation and runner-captured logs were read directly to establish/use the logging interface; substantive input/source/API/build/audit/bookkeeping operations used the provided runner and write_lane.py. No retrospective success receipt is invented for the initial failed commands.

See results/keyed-results.json, results/deep-audit.json, results/full-manifest.json, manuscript/polynexus-proof.md and cleanroom/setup.json for concrete evidence.
'''
write('SUMMARY.md',summary)
write('CHECKPOINT.md',summary)
p=Path('manuscript/polynexus-proof.md');s=p.read_text().replace('the separate Raw audit emits full expression nodes, including binder information, universes, metadata and child references. Final keyed results record its actual outcome and all receipts.','the attempted Raw audit hit the CPU limit and is preserved as failed. Sixteen disjoint exhaustive hash partitions of the same full closure instead emit types and opaque bodies with pp.all, pp.privateNames, pp.deepTerms and a raised pretty-printer step limit. Coverage reconciliation verifies all 7,003 declarations appear exactly once in the unabridged body output, with zero abbreviation symbols. Final keyed results record all actual outcomes and receipts.');write(str(p),s)
log=Path(os.readlink('/proc/self/fd/1')).relative_to(lane)
receipt=Path('receipt')/(log.stem+'.json')
excluded=['results/full-manifest.json',str(log),str(receipt)]
manifest={'self_exclusions':{excluded[0]:'manifest cannot hash itself',excluded[1]:'currently open terminal bookkeeping log',excluded[2]:'terminal receipt is written by runner after this manifest'},'files':{}}
for p in sorted(lane.rglob('*')):
 if p.is_file() and str(p.relative_to(lane)) not in excluded:
  manifest['files'][str(p.relative_to(lane))]={'sha256':digest(p),'bytes':p.stat().st_size}
put('results/full-manifest.json',manifest)
print(json.dumps({'complete':True,'manifest_files':len(manifest['files']),'self_exclusions':excluded,'credit':0,'accepted':'52/60'}))
