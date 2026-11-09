"""Root documentary verification of 338806 formal r6 and preparation of the sealed-baseline r7 continuation; no root mathematics or Lean execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
F=P/'high-girth-ur-matching-formal-sol-r6';L=P/'high-girth-ur-matching-formal-sol-r7';assert not L.exists()
def jsonrows(q):
 out=[]
 for line in q.read_text(errors='replace').splitlines():
  try:v=json.loads(line)
  except ValueError:continue
  if isinstance(v,dict):out.append(v)
 return out

# Every documentary check precedes any root mutation.
fex=manifest(F,'MANIFEST.json',749,'terminal_manifest_094','terminal_non_circular_exclusions');frozen(F,469)
man=read(F/'MANIFEST.json');assert man['credit']==0 and man['scientific_status']=='HOLD' and man['literal_endpoint'] is False
assert sha(F/'TASK.txt')==read(ROOT/'high-girth-ur-matching-formal-r6-ready.json')['task_sha256']
failures={n+'.receipt.json':1 for n in ['witness_axioms_009','distinct_core_compile_018','bound_compile_028','bound_nat_compile_031','moment_compile_038','moment_compile_041','moment_compile_043','moment_compile_045','weighted_compile_051','weighted_compile_053','removed_compile_063','graph_split_compile_075','graph_compile_077','degree_compile_082','degree_compile_084']}
for n in ['distinct_compile_013','distinct_reduced_compile_015','graph_compile_073']:failures[n+'.receipt.json']=250
frec=receipts(F,failures);assert read(F/'terminal_manifest_094.receipt.json')['exit']==0
pins=read(F/'PINS.json');result=read(F/'results/338806.json');base=read(F/'BASELINE.json')
assert result['formal_status']=='INCOMPLETE_NO_LITERAL_ENDPOINT' and result['credit']==0 and result['scientific_status']=='HOLD' and result['technical_pass'] is False
for row in base['immutable_green_modules']:assert sha(F/'src'/(row['module']+'.lean'))==row['source_sha256'] and sha(F/'build'/(row['module']+'.olean'))==row['olean_sha256']
bn=[x['module'] for x in base['immutable_green_modules']];assert len(bn)==25
cert=result['r6_certified'];new=[x for x in result['strict_green_modules'] if x not in bn];assert len(new)==12 and set(new)==set(cert) and len(result['strict_green_modules'])==37
trio={'propext','Classical.choice','Quot.sound'};green=[]
for module in new:
 cl,kl,al=cert[module]['compile'],cert[module]['checker'],cert[module]['axioms']
 c=next(x for x in jsonrows(F/(cl+'.output.txt')) if x.get('stage')=='compile' and x.get('module')==module)
 k=next(x for x in jsonrows(F/(kl+'.output.txt')) if x.get('stage')=='check' and x.get('module')==module)
 assert c['exit']==k['exit']==read(F/(cl+'.receipt.json'))['exit']==read(F/(kl+'.receipt.json'))['exit']==read(F/(al+'.receipt.json'))['exit']==0
 source=sha(F/'src'/(module+'.lean'));olean=sha(F/'build'/(module+'.olean'))
 assert c['source_sha256_before']==c['source_sha256_after']==k['source_sha256_before']==k['source_sha256_after']==source and c['olean_sha256_after']==k['olean_sha256_before']==k['olean_sha256_after']==olean
 assert c['argv'][0]==pins['lean_bin'] and all(x in c['argv'] for x in ['-j1','-M3500','-DwarningAsError=true']) and k['argv']==[pins['leanchecker_bin'],module]
 assert c['LEAN_PATH']==k['LEAN_PATH']==':'.join([str(F/'build')]+pins['upstream_lean_paths']) and c['LEAN_NUM_THREADS']==k['LEAN_NUM_THREADS']==1
 found=re.findall(r'depends on axioms: \[([^\]]*)\]',(F/(al+'.output.txt')).read_text(errors='replace'));assert found,al
 assert all({y.strip() for y in f.split(',')}<=trio for f in found),al
 assert result['r6_hashes']['src/'+module+'.lean']==source and result['r6_hashes']['build/'+module+'.olean']==olean
 green.append(dict(module=module,source_sha256=source,olean_sha256=olean,compile=cl,checker=kl,axioms=al,compile_receipt_sha256=sha(F/(cl+'.receipt.json')),checker_receipt_sha256=sha(F/(kl+'.receipt.json'))))
for q in F.glob('*.output.txt'):assert 'sorryAx' not in q.read_text(errors='replace'),q.name
allrows=base['immutable_green_modules']+green;assert len(allrows)==37
for row in allrows:
 text=(F/'src'/(row['module']+'.lean')).read_text();assert not re.search(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|^\s*axiom\b',text,re.M),row['module']
fs='338806 uncredited formal r6 INCOMPLETE, no literal negation, no paper, no technical PASS. Twelve new strict compile plus kernel green modules with scoped axioms verified byte/log/receipt on top of twenty-five sealed baseline modules, thirty-seven in all. Paid: coloured-cycle and parallel witness occurrence is exactly independent per-colour restrictions with exact factorial-product count, zero when inconsistent; valid occurring witnesses have exactly 2(k+1) distinct coloured-input prescriptions; the individual probability bound, per-length and weighted first moment and finite Markov; for every cutoff h an actual 100-permutation tuple with no a-square hole and 100*weight<4a, with no good-tuple premise; deletion of all vertices on all occurring witnesses with union cardinal at most the weight; no surviving parallel pair at positive cutoff; and the actual induced simple survivor graph, bipartition, all-vertex degree at most 100 and no-hole adjacency transport on surviving label subsets. Unpaid: genuine Walk.IsCycle extraction into witness descriptions, evenness, destruction of all short cycles and girth; the induced first-colour matching and retained cardinal; transport of the obstruction to all survivor UR matchings and the strict real ratio; standard matching, degree, source, forest, universe, relabeling and coding bridges; the universal literal negation; full audits, controls, empty-build replay, paper, independent review and root scientific adjudication. Three compile runs failed with failed to create thread, repaired by simplification and splitting without raising limits. 749 manifest files, 469 frozen bindings, 37 modules verified; no root Lean execution. Scientific HOLD and credit 0 unchanged, 57/60.'
fr=dict(utc=now,mathdb_id=338806,source_lane=str(F),manifest_sha256=sha(F/'MANIFEST.json'),verified_manifest_files=749,verified_frozen_bindings=469,green_modules=allrows,new_green_modules=green,runner_receipts=frec,body_audit_unpaid=True,result=result,scientific_summary=fs,root_disposition='INCOMPLETE_UNCREDITED_FORMAL_RESEARCH_CONTINUE',credit=0,accepted_new=57,terminal_self_exclusions=fex,root_scope='Documentary integrity only; no Lean/math execution by root.')
den=read(ROOT/'inherited-denials-r535.json');den['utc']=now;den['root_highgirth338806_formal_r6_scope']=fs
save(P/'high-girth-ur-matching-formal-parent-integration-r6.json',fr);denpath=ROOT/'inherited-denials-r536.json';save(denpath,den)
save(ROOT/'formal-r6-intake-report.json',dict(utc=now,files=749,frozen=469,verified_green_modules=allrows,credit=0,accepted_new=57,no_root_mathematics=True))

L.mkdir();origins={}
def copy(src,rel):
 dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]=dict(path=str(src),sha256=sha(src))
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','model-policy-sol-only.json','PINS.json','formal_command.py','check.sh','checker.sh']:copy(F/h,h)
for h in ['check.sh','checker.sh']:(L/h).chmod(0o755)
for d in ['src','build','cache','audit','receipt','logs','results','cleanroom/src','cleanroom/build','manuscript','output/pdf']:(L/d).mkdir(parents=True,exist_ok=True)
for q in (F/'inputs').rglob('*'):
 if q.is_file():
  rel=Path('inputs')/q.relative_to(F/'inputs');s=str(rel)
  if s=='inputs/ROOT-AUTHORIZATION.json':rel=Path('inputs/PREVIOUS-ROOT-AUTHORIZATION-r6.json')
  elif s=='inputs/INHERITED-DENIALS.json':continue
  copy(q,str(rel))
copy(denpath,'inputs/INHERITED-DENIALS.json')
baseline=[]
for row in allrows:
 module=row['module'];copy(F/'src'/(module+'.lean'),'src/'+module+'.lean')
 blobs=[]
 for q in (F/'build').glob(module+'.*'):
  if q.is_file():copy(q,'build/'+q.name);blobs.append(dict(path='build/'+q.name,sha256=sha(q)))
 assert sha(L/'src'/(module+'.lean'))==row['source_sha256'] and sha(L/'build'/(module+'.olean'))==row['olean_sha256']
 baseline.append(dict(row,blobs=blobs))
for q in sorted((F/'audit').glob('*.lean')):copy(q,'inputs/drafts-r6/'+q.name)
labels=set()
for row in green:labels.update([row['compile'],row['checker'],row['axioms']])
labels.update(n[:-len('.receipt.json')] for n in failures)
for label in sorted(labels):
 for suffix in ['.receipt.json','.output.txt']:copy(F/(label+suffix),'inputs/previous-receipts-r6/'+label+suffix)
for name in ['SUMMARY.md','CHECKPOINT.md','results/338806.json','source-to-literal-map.json']:copy(F/name,'inputs/previous-r6/'+Path(name).name)
save(L/'BASELINE.json',dict(origin=str(F),root_verified_manifest_sha256=sha(F/'MANIFEST.json'),immutable_green_modules=baseline,uncompiled_or_uncertified_drafts='inputs/drafts, inputs/drafts-r4, inputs/drafts-r5 and inputs/drafts-r6 only; NOT paid theorem/source endpoint',rule='Own copied baseline source and all compiler sidecars are immutable; do not rewrite or recompile these in production. Import own-build sealed oleans. Final empty-build source-only replay must rebuild copied source plus new source with no production or legacy paths. No external origin paths may be followed.'))
authorization=dict(utc=now,mathdb_id=338806,status='CONTINUE_UNCOUNTED_FORMAL_RESEARCH_INCOMPLETE_SCIENTIFIC_HOLD_PRESERVED',authority='Continuation of existing user-authorized literal Lean research; latest user message: keep progress. No additional acceptance or scientific waiver.',previous_authorization=str(P/'high-girth-ur-matching-formal-research-authorization-r6.json'),basis='Root documentary verification confirms thirty-seven strict and kernel green modules and no literal endpoint. Continue the actual unpaid pipeline without repeating green baseline.',scientific_status='HOLD remains; final, prior and significance gates can veto credit. No source-access waiver implied by formal progress.',paid=[x['module'] for x in baseline],unpaid=result['unpaid'],credit=0,accepted_new=57,target_new=60,root_Lean_or_math_execution=False)
save(P/'high-girth-ur-matching-formal-research-authorization-r7.json',authorization);save(L/'inputs/ROOT-AUTHORIZATION.json',authorization)
peers=['expanded-corpus-r516','expanded-corpus-r517']
task=(F/'TASK.txt').read_text().replace(str(F),str(L)).replace('expanded-corpus-r515',peers[0]).replace('parking-strong-a2-formal-sol-r1',peers[1])
override=f'''R7 CONTINUATION OVERRIDE. GPT-6.1 Sol HIGH/DEFAULT ONLY, no children, offline uncredited research. Scientific HOLD, credit 0 and 57 of 60 unchanged. This override supersedes the earlier R3 to R6 first-new-proof, base-writing and baseline-replay instructions in the inherited TASK below; every other source, model, cap, audit, replay and acceptance restriction remains. The full literal endpoint is still unpaid; do not stop at another helper or control milestone.

FIRST command EXACTLY: timeout 20 python3 -I -B {L}/bootstrap.py
SECOND command EXACTLY: timeout 140 python3 -I -B {L}/verify_frozen.py before
Then use only your own immutable capped runner, writer and wrappers. Active peers {peers[0]} and {peers[1]} are entirely protected, including metadata, stat, hash, list, glob, poll, reservations and flat integrations. R3 to R6 and all other lanes are now external and protected, even baseline origin paths: your own copies only, plus pinned upstream APIs. No network, source queries, git, install, accounts, browser, other models, mathematical programs, solvers, shared or tmp writes, or background jobs. PINS, helpers and baseline are frozen and never overwritten.

Read BASELINE.json, inputs/ROOT-AUTHORIZATION.json, inputs/previous-r6/CHECKPOINT.md, inputs/previous-r6/338806.json and the source-to-literal map, and selected receipts and the author and independent proofs. The THIRTY-SEVEN baseline modules listed in BASELINE.json and every own-build compiler sidecar are IMMUTABLE; root verified their actual strict compile and checker hashes and receipts. Do not rewrite or recompile them unchanged and do not run check.sh on these names. The final cleanroom replay must freshly build ALL baseline SOURCE plus new modules from an empty own build with upstream only and no production, legacy or author paths. If a genuine baseline fidelity error arises, disclose it precisely and add new faithful definitions or proved generic bridges without mutating the frozen baseline or assuming the endpoint.

FIRST NEW-PROOF work after the mandatory read and pin check must advance the first UNPAID real item below, with an immediate strict compile and kernel check, before broad API or planning tours. Follow the copied complete independent PROOF, not an invented weakened question. Work in ordinary proof order:
1. Genuine Walk.IsCycle extraction into alternating ordered witness descriptions (URMatchingCycleDescriptions), evenness in the bipartite graph, destruction of all short cycles in the induced survivor, and genuine girth with the forest and source conventions.
2. The induced survivor first-colour matching and its retained cardinal greater than 99N/100, using that the first colour loses at most one edge per deleted vertex.
3. Transport of the no-hole obstruction to all actual survivor UR matchings through URMatching.ur_partition_empty_rectangle, and the strict real ratio.
4. Standard subgraph matching and matching-number correspondence, the standard all-vertex degree correspondence, and the generic induced graph to standard induce correspondence.
5. Finite-type, universe, relabeling and canonical-coding bridges and the universal literal negation.
If real budget remains after the endpoint, begin the unpaid audits, controls and empty-build replay. No assumed good tuple, no holes, expander, probability existence, conclusion-bearing premise or finite enumeration encoding the answer. Existing green modules are not the endpoint.

inputs/drafts-r4/URMatchingSource.lean is an input only and NOT certified. Across R4 to R6, import-heavy modules hit unreadable upstream oleans, bad_alloc and failed-to-create-thread errors, and those were repaired only by changed import graphs, simplification or splitting. Use minimal imports and small modules, certify source conventions through a changed import graph or genuinely repaired source, and never retry unchanged. No cap or limit increase is authorized. Every Lean or audit process uses -j1, -M3500 or stricter, LEAN_NUM_THREADS 1 and the same AS 6GiB, RSS 6GiB and CPU 115 caps. Preserve every failure with its true exit. Every new green module needs compile, checker, scoped axioms and a checkpoint with exact source, olean, log and receipt hashes, with no future-tense handback. Keep results/338806.json strict_green_modules complete. If interrupted, persist actual new mathematical sources, the last real diagnostics and a precise unpaid ledger.

The manuscript, PDF, full body audits, controls, full source-only replay, source-fidelity review, independent review and root scientific adjudication are unpaid. No paper exists; make no misleading reuse claim. Scientific HOLD must stay explicit in results and any manuscript. Source 1803.11032 and final DOI 10.1007/s00373-018-1991-8 are closed to new deliveries. A final technical PASS comes only after the actual endpoint, all bridges, replay and audits; acceptance and credit are root-only and may be refused. Seal standalone frozen-after, then an exhaustive own-byte manifest including baseline sidecars, new sources, all completed receipts, inputs, audits and any paper, with exact terminal noncircular exclusions. Credit 0, 57 of 60 unchanged.

INHERITED FULL TASK (the override above controls all conflicts):
'''
(L/'TASK.txt').write_text(override+task)
save(L/'INPUT-ORIGINS.json',origins);save(L/'ROOT-PREP.json',dict(utc=now,lane=str(L),mathdb_id=338806,model='gpt-6.1-sol',reasoning='high',service='default',scientific_hold=True,credit=0,accepted_new=57,children=False,network=False,root_math_or_Lean_execution=False,protected_peers=peers))
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=338806,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),baseline_modules=len(baseline),model='gpt-6.1-sol',reasoning='high',service='default',credit=0,accepted_new=57,scientific_hold=True,protected_peers=peers)
save(ROOT/'high-girth-ur-matching-formal-r7-ready.json',ready);save(ROOT/'selection-routing-high-girth-ur-matching-formal-r7.json',dict(ids=[338806],sources=['https://arxiv.org/abs/1803.11032'],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
print(json.dumps(dict(r6_manifest=749,frozen=469,green=len(allrows),r7=ready,credit=0,accepted_new=57)))
