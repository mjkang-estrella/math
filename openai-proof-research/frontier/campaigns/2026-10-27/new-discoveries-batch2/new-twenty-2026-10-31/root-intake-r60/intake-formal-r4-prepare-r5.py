"""Root documentary verification of 338806 formal r4 and preparation of the sealed-baseline r5 continuation; no root mathematics or Lean execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
F=P/'high-girth-ur-matching-formal-sol-r4';L=P/'high-girth-ur-matching-formal-sol-r5';assert not L.exists()
def jsonrows(q):
 out=[]
 for line in q.read_text().splitlines():
  try:v=json.loads(line)
  except ValueError:continue
  if isinstance(v,dict):out.append(v)
 return out

# Every documentary check precedes any root mutation.
fex=manifest(F,'MANIFEST.json',477,'r4_terminal_manifest_114','terminal_non_circular_exclusions');frozen(F,121)
assert sha(F/'TASK.txt')==read(ROOT/'high-girth-ur-matching-formal-r4-ready.json')['task_sha256']
failures={n+'.receipt.json':1 for n in ['r4_source_first_007','r4_source_kernel_010','r4_embedded_first_017','r4_embedded_fixed_019','r4_embedded_kernel_020','r4_embedded_green_022','r4_embedded_compile_024','r4_cycle_first_037','r4_cycle_fix_compile_039','r4_rectangle_first_048','r4_dag_first_055','r4_extract_first_064','r4_extract_fixed_066','r4_extract_compile_068','r4_orientation_first_078','r4_partition_kernel_096','r4_partition_checkpoint_097','r4_count_first_100']};failures['r4_embedded_kernel_027.receipt.json']=250
frec=receipts(F,failures);assert read(F/'r4_terminal_manifest_114.receipt.json')['exit']==0
pins=read(F/'PINS.json');result=read(F/'results/338806.json');base=read(F/'BASELINE.json')
assert result['formal_status']=='INCOMPLETE_NO_LITERAL_ENDPOINT' and result['credit']==0 and result['scientific_status']=='HOLD' and result['technical_pass'] is False
pairs=[('URMatchingSwitch','r4_switch_first_013','r4_switch_kernel_014'),('URMatchingEmbeddedSwitch','r4_embedded_reduced_031','r4_embedded_reduced_kernel_032'),('URMatchingDirectedCycle','r4_cycle_compile_041','r4_cycle_kernel_042'),('URMatchingRectangle','r4_rectangle_compile_050','r4_rectangle_kernel_051'),('URMatchingDAG','r4_dag_fixed_060','r4_dag_kernel_061'),('URMatchingCycleExtraction','r4_extract_green_070','r4_extract_kernel_071'),('URMatchingURRectangle','r4_urrect_first_074','r4_urrect_kernel_075'),('URMatchingOrientation','r4_orientation_compile_080','r4_orientation_kernel_081'),('URMatchingRectangleSides','r4_sides_compile_084','r4_sides_kernel_085'),('URMatchingURSides','r4_ursides_compile_088','r4_ursides_kernel_089'),('URMatchingOrientationSides','r4_orientsides_compile_091','r4_orientsides_kernel_092'),('URMatchingIndependentCount','r4_count_fixed_103','r4_count_kernel_104'),('URMatchingPartition','r4_partitionlemma_compile_107','r4_partitionlemma_kernel_108'),('URMatchingBipartiteObstruction','r4_partition_split_compile_110','r4_partition_split_kernel_111')]
green=[]
for module,cl,kl in pairs:
 c=next(x for x in jsonrows(F/(cl+'.output.txt')) if x.get('stage')=='compile' and x.get('module')==module)
 k=next(x for x in jsonrows(F/(kl+'.output.txt')) if x.get('stage')=='check' and x.get('module')==module)
 assert c['exit']==k['exit']==read(F/(cl+'.receipt.json'))['exit']==read(F/(kl+'.receipt.json'))['exit']==0
 source=sha(F/'src'/(module+'.lean'));olean=sha(F/'build'/(module+'.olean'))
 assert c['source_sha256_before']==c['source_sha256_after']==k['source_sha256_before']==k['source_sha256_after']==source
 assert c['olean_sha256_after']==k['olean_sha256_before']==k['olean_sha256_after']==olean
 assert c['argv'][0]==pins['lean_bin'] and all(x in c['argv'] for x in ['-j1','-M3500','-DwarningAsError=true']) and k['argv']==[pins['leanchecker_bin'],module]
 assert c['LEAN_PATH']==k['LEAN_PATH']==':'.join([str(F/'build')]+pins['upstream_lean_paths']) and c['LEAN_NUM_THREADS']==k['LEAN_NUM_THREADS']==1
 green.append(dict(module=module,source_sha256=source,olean_sha256=olean,compile=cl,checker=kl,compile_receipt_sha256=sha(F/(cl+'.receipt.json')),checker_receipt_sha256=sha(F/(kl+'.receipt.json'))))
for row in base['immutable_green_modules']:assert sha(F/'src'/(row['module']+'.lean'))==row['source_sha256'] and sha(F/'build'/(row['module']+'.olean'))==row['olean_sha256']
allrows=base['immutable_green_modules']+green;assert result['strict_green_modules']==[x['module'] for x in allrows] and len(allrows)==18
trio={'propext','Classical.choice','Quot.sound'}
for q in sorted((F/'audit').iterdir()):
 text=q.read_text();found=re.findall(r'depends on axioms: \[([^\]]*)\]',text);assert found and 'sorryAx' not in text,q.name
 assert all({x.strip() for x in f.split(',')}<=trio for f in found),q.name
for row in allrows:
 text=(F/'src'/(row['module']+'.lean')).read_text();assert not re.search(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|^\s*axiom\b',text,re.M),row['module']
fs='338806 uncredited formal r4 INCOMPLETE, no literal negation, no paper, no technical PASS. Fourteen new strict compile plus kernel green modules verified byte/log/receipt, on top of four frozen baseline modules, eighteen in all: directed-cycle switch on embedded partial matchings, cycle extraction from closed TransGen walks, finite DAG ranking, exact floor(card M/2) empty rectangles, and the assembled URMatching.ur_partition_empty_rectangle for any matching in a properly two-coloured graph; plus the full 100-permutation sample space with exact fixed-rectangle factorization. That factorization does NOT pay the one-colour estimate, union bound or good-tuple existence. URMatchingSource compiled but its checker exited 1 on an unreadable upstream Cardinal/Finite.olean.private, so it is NOT certified. All retained failures verified, including embedded kernel 027 bad_alloc (Lean -6 / runner 250) and partition kernel 096 out of memory, both repaired only by changed sources. Scoped axiom prints show the permitted trio only and are NOT a full transitive body audit. Unpaid: one-colour count and rectangle union bound; coloured-cycle and parallel first moment; finite existence for every girth; induced survivor, degree, girth, no-hole, relabeling and matching transport; matching, degree and source bridges; strict real ratio and universal literal negation; full audits, controls, empty-build replay, paper, independent review and root scientific adjudication. 477 manifest files, 121 frozen bindings, 18 green modules verified; no root Lean execution. Scientific HOLD and credit 0 unchanged, 57/60.'
fr=dict(utc=now,mathdb_id=338806,source_lane=str(F),manifest_sha256=sha(F/'MANIFEST.json'),verified_manifest_files=477,verified_frozen_bindings=121,green_modules=allrows,new_green_modules=green,runner_receipts=frec,body_audit_unpaid=True,result=result,scientific_summary=fs,root_disposition='INCOMPLETE_UNCREDITED_FORMAL_RESEARCH_CONTINUE',credit=0,accepted_new=57,terminal_self_exclusions=fex,root_scope='Documentary integrity only; no Lean/math execution by root.')
den=read(ROOT/'inherited-denials-r528.json');den['utc']=now;den['root_highgirth338806_formal_r4_scope']=fs
save(P/'high-girth-ur-matching-formal-parent-integration-r4.json',fr);denpath=ROOT/'inherited-denials-r529.json';save(denpath,den)
save(ROOT/'formal-r4-intake-report.json',dict(utc=now,files=477,frozen=121,verified_green_modules=allrows,credit=0,accepted_new=57,no_root_mathematics=True))

L.mkdir();origins={}
def copy(src,rel):
 dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]=dict(path=str(src),sha256=sha(src))
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','model-policy-sol-only.json','PINS.json','formal_command.py','check.sh','checker.sh']:copy(F/h,h)
for h in ['check.sh','checker.sh']:(L/h).chmod(0o755)
for d in ['src','build','cache','audit','receipt','logs','results','cleanroom/src','cleanroom/build','manuscript','output/pdf']:(L/d).mkdir(parents=True,exist_ok=True)
for q in (F/'inputs').rglob('*'):
 if q.is_file():
  rel=Path('inputs')/q.relative_to(F/'inputs');s=str(rel)
  if s=='inputs/ROOT-AUTHORIZATION.json':rel=Path('inputs/PREVIOUS-ROOT-AUTHORIZATION-r4.json')
  elif s=='inputs/PREVIOUS-ROOT-AUTHORIZATION.json':rel=Path('inputs/PREVIOUS-ROOT-AUTHORIZATION-r3.json')
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
copy(F/'src/URMatchingSource.lean','inputs/drafts-r4/URMatchingSource.lean')
for q in sorted((F/'src').glob('*Axioms.lean')):copy(q,'inputs/drafts-r4/'+q.name)
labels={'r4_read_004'}
for row in green:labels.update([row['compile'],row['checker']])
labels.update(n[:-len('.receipt.json')] for n in failures)
for label in sorted(labels):
 for suffix in ['.receipt.json','.output.txt']:copy(F/(label+suffix),'inputs/previous-receipts-r4/'+label+suffix)
for name in ['SUMMARY.md','CHECKPOINT.md','results/338806.json','source-to-literal-map.json']:copy(F/name,'inputs/previous-r4/'+Path(name).name)
for q in sorted((F/'audit').iterdir()):copy(q,'inputs/previous-r4/audit/'+q.name)
save(L/'BASELINE.json',dict(origin=str(F),root_verified_manifest_sha256=sha(F/'MANIFEST.json'),immutable_green_modules=baseline,uncompiled_or_uncertified_drafts='inputs/drafts and inputs/drafts-r4 only; NOT paid theorem/source endpoint',rule='Own copied baseline source and all compiler sidecars are immutable; do not rewrite or recompile these in production. Import own-build sealed oleans. Final empty-build source-only replay must rebuild copied source plus new source with no production or legacy paths. No external origin paths may be followed.'))
authorization=dict(utc=now,mathdb_id=338806,status='CONTINUE_UNCOUNTED_FORMAL_RESEARCH_INCOMPLETE_SCIENTIFIC_HOLD_PRESERVED',authority='Continuation of existing user-authorized literal Lean research; latest user message: keep progress. No additional acceptance or scientific waiver.',previous_authorization=str(P/'high-girth-ur-matching-formal-research-authorization-r4.json'),basis='Root documentary verification confirms eighteen strict and kernel green modules and no literal endpoint. Continue the actual unpaid pipeline without repeating green baseline.',scientific_status='HOLD remains; final, prior and significance gates can veto credit. No source-access waiver implied by formal progress.',paid=[x['module'] for x in baseline],unpaid=result['unpaid'],credit=0,accepted_new=57,target_new=60,root_Lean_or_math_execution=False)
save(P/'high-girth-ur-matching-formal-research-authorization-r5.json',authorization);save(L/'inputs/ROOT-AUTHORIZATION.json',authorization)
peers=['nfm-dirichlet-psd-source-review-sol-r1','parking-strong-a2-source-review-sol-r1']
task=(F/'TASK.txt').read_text().replace(str(F),str(L)).replace('expanded-corpus-r513',peers[0]).replace('expanded-corpus-r514',peers[1])
override=f'''R5 CONTINUATION OVERRIDE. GPT-6.1 Sol HIGH/DEFAULT ONLY, no children, offline uncredited research. Scientific HOLD, credit 0 and 57 of 60 unchanged. This override supersedes the earlier R3 and R4 first-new-proof, base-writing and baseline-replay instructions in the inherited TASK below; every other source, model, cap, audit, replay and acceptance restriction remains. The full literal endpoint is still unpaid; do not stop at another helper or control milestone.

FIRST command EXACTLY: timeout 20 python3 -I -B {L}/bootstrap.py
SECOND command EXACTLY: timeout 140 python3 -I -B {L}/verify_frozen.py before
Then use only your own immutable capped runner, writer and wrappers. Active peers {peers[0]} and {peers[1]} are entirely protected, including metadata, stat, hash, list, glob, poll, reservations and flat integrations. R3, R4 and all other lanes are now external and protected, even baseline origin paths: your own copies only, plus pinned upstream APIs. No network, source queries, git, install, accounts, browser, other models, mathematical programs, solvers, shared or tmp writes, or background jobs. PINS, helpers and baseline are frozen and never overwritten.

Read BASELINE.json, inputs/ROOT-AUTHORIZATION.json, inputs/previous-r4/CHECKPOINT.md, inputs/previous-r4/338806.json and source-to-literal-map.json, and selected receipts and the author and independent proofs. The EIGHTEEN baseline modules (Base, Finite, Deletion, Controls, Switch, EmbeddedSwitch, DirectedCycle, Rectangle, DAG, CycleExtraction, URRectangle, Orientation, RectangleSides, URSides, OrientationSides, IndependentCount, Partition, BipartiteObstruction) and every own-build compiler sidecar are IMMUTABLE. Root verified their actual strict compile and checker hashes and receipts. Do not rewrite or recompile them unchanged and do not run check.sh on these names. Use own-build sealed imports only. The final cleanroom replay must freshly build ALL baseline SOURCE plus new modules from an empty own build with upstream only and no production, legacy or author paths. If a genuine baseline fidelity error arises, disclose it precisely and add new faithful definitions or proved generic bridges without mutating the frozen baseline or assuming the endpoint.

FIRST NEW-PROOF work after the mandatory read and pin check must advance the first UNPAID real item below, with an immediate strict compile and kernel check, before broad API or planning tours. Follow the copied complete independent PROOF, not an invented weakened question. Work in ordinary proof order:
1. One-colour permutation avoidance: the exact factorial/falling-factorial count and a sufficient bound, then the union bound over all rectangle choices and the eventual strict hole estimate. URMatchingIndependentCount proves only the exact factorization of the fixed-rectangle avoidance count into the one-colour count to the power 100.
2. Coloured short-cycle and parallel witnesses, the prescription-consistency count and the first-moment bound.
3. Finite Markov and union existence of an actual tuple for every girth at fixed degree 100.
4. The induced survivor construction: simplicity, degree, no holes, genuine cycle and girth transport, relabeling and matching retention. The existing Deletion module covers only original-graph lost-edge cardinality.
5. Standard subgraph matching and matching-number correspondence, the standard all-vertex degree bridge, genuine Walk.IsCycle, forest and source conventions, and finite-type, universe, relabeling and canonical-coding bridges.
6. The strict real ratio and the universal literal negation.
No assumed good tuple, no holes, expander, probability existence, conclusion-bearing premise or finite enumeration encoding the answer. Existing green modules are not the endpoint.

URMatchingSource strict compiled in R4 but its kernel check r4_source_kernel_010 exited 1 on an unreadable upstream Cardinal/Finite.olean.private, so it is NOT certified. inputs/drafts-r4/URMatchingSource.lean is an input only. Certify the source conventions through a changed import graph or genuinely repaired source, not an unchanged retry. Kernel failures in R4 (embedded 027 bad_alloc, partition 096 out of memory) were repaired only by dropping unused imports or splitting modules, so keep modules small and imports minimal. No cap or limit increase. Every Lean or audit process uses -j1, -M3500 or stricter, LEAN_NUM_THREADS 1 and the same AS 6GiB, RSS 6GiB and CPU 115 caps. Preserve every failure with its true exit. Every new green module needs compile, checker, scoped axioms and a checkpoint with exact source, olean, log and receipt hashes, with no future-tense handback. If interrupted, persist actual new mathematical sources, the last real diagnostics and a precise unpaid ledger.

The manuscript, PDF, full body audits, controls, full source-only replay, source-fidelity review, independent review and root scientific adjudication are unpaid. No paper exists; make no misleading reuse claim. Scientific HOLD must stay explicit in results and any manuscript. Source 1803.11032 and final DOI 10.1007/s00373-018-1991-8 are closed to new deliveries. A final technical PASS comes only after the actual endpoint, all bridges, replay and audits; acceptance and credit are root-only and may be refused. Seal standalone frozen-after, then an exhaustive own-byte manifest including baseline sidecars, new sources, all completed receipts, inputs, audits and any paper, with exact terminal noncircular exclusions. Credit 0, 57 of 60 unchanged.

INHERITED FULL TASK (the override above controls all conflicts):
'''
(L/'TASK.txt').write_text(override+task)
save(L/'INPUT-ORIGINS.json',origins);save(L/'ROOT-PREP.json',dict(utc=now,lane=str(L),mathdb_id=338806,model='gpt-6.1-sol',reasoning='high',service='default',scientific_hold=True,credit=0,accepted_new=57,children=False,network=False,root_math_or_Lean_execution=False,protected_peers=peers))
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=338806,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),baseline_modules=len(baseline),model='gpt-6.1-sol',reasoning='high',service='default',credit=0,accepted_new=57,scientific_hold=True,protected_peers=peers)
save(ROOT/'high-girth-ur-matching-formal-r5-ready.json',ready);save(ROOT/'selection-routing-high-girth-ur-matching-formal-r5.json',dict(ids=[338806],sources=['https://arxiv.org/abs/1803.11032'],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
print(json.dumps(dict(r4_manifest=477,frozen=121,green=len(allrows),r5=ready,credit=0,accepted_new=57)))
