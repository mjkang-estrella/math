"""Root documentary verification of 338806 formal r7, consolidated kernel-failure evidence and the sealed-baseline r8 continuation; no root mathematics or Lean execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
F=P/'high-girth-ur-matching-formal-sol-r7';L=P/'high-girth-ur-matching-formal-sol-r8';assert not L.exists()
def jsonrows(q):
 out=[]
 for line in q.read_text(errors='replace').splitlines():
  try:v=json.loads(line)
  except ValueError:continue
  if isinstance(v,dict):out.append(v)
 return out

# Every documentary check precedes any root mutation.
fex=manifest(F,'MANIFEST.json',818,'r7_manifest_047','terminal_noncircular_exclusions');frozen(F,667)
man=read(F/'MANIFEST.json');assert man['credit']==0 and man['scientific_status']=='HOLD' and man['count']==818
assert sha(F/'TASK.txt')==read(ROOT/'high-girth-ur-matching-formal-r7-ready.json')['task_sha256']
failures={n+'.receipt.json':1 for n in ['r7_parity_compile_006','r7_parity_kernel_009','r7_checkpoint_parity_014','r7_positions_compile_023','r7_positions_diagnostic_025','r7_labels_compile_031','r7_walkdescription_compile_037','r7_genuine_kernel_044']}
frec=receipts(F,failures);assert read(F/'r7_manifest_047.receipt.json')['exit']==0
pins=read(F/'PINS.json');result=read(F/'results/338806.json');base=read(F/'BASELINE.json')
assert result['formal_status']=='INCOMPLETE_PARTIAL_PROGRESS_GENUINE_CYCLE_KERNEL_BLOCKED' and result['credit']==0 and result['scientific_status']=='HOLD' and result['technical_pass'] is False
for row in base['immutable_green_modules']:assert sha(F/'src'/(row['module']+'.lean'))==row['source_sha256'] and sha(F/'build'/(row['module']+'.olean'))==row['olean_sha256']
bn=[x['module'] for x in base['immutable_green_modules']];assert len(bn)==37
pairs=[('URMatchingWalkParity','r7_parity_compile_012','r7_parity_kernel_013','WalkParityModularAxioms.txt','r7_checkpoint_parity_015'),('URMatchingOrderedCycle','r7_ordered_compile_018','r7_ordered_kernel_019','OrderedCycleAxioms.txt','r7_ordered_checkpoint_020'),('URMatchingWalkPositions','r7_positions_compile_027','r7_positions_kernel_028','WalkPositionsAxioms.txt','r7_positions_checkpoint_029'),('URMatchingWalkLabels','r7_labels_compile_033','r7_labels_kernel_034','WalkLabelsAxioms.txt','r7_labels_checkpoint_035'),('URMatchingWalkDescription','r7_walkdescription_compile_039','r7_walkdescription_kernel_040','WalkDescriptionAxioms.txt','r7_walkdescription_checkpoint_041')]
assert [p[0] for p in pairs]==result['r7_certified'] and result['strict_green_modules']==bn+[p[0] for p in pairs]
trio={'propext','Classical.choice','Quot.sound'};green=[]
for module,cl,kl,axf,ckpt in pairs:
 c=next(x for x in jsonrows(F/(cl+'.output.txt')) if x.get('stage')=='compile' and x.get('module')==module)
 k=next(x for x in jsonrows(F/(kl+'.output.txt')) if x.get('stage')=='check' and x.get('module')==module)
 assert c['exit']==k['exit']==read(F/(cl+'.receipt.json'))['exit']==read(F/(kl+'.receipt.json'))['exit']==read(F/(ckpt+'.receipt.json'))['exit']==0
 source=sha(F/'src'/(module+'.lean'));olean=sha(F/'build'/(module+'.olean'))
 assert c['source_sha256_before']==c['source_sha256_after']==k['source_sha256_before']==k['source_sha256_after']==source and c['olean_sha256_after']==k['olean_sha256_before']==k['olean_sha256_after']==olean
 assert c['argv'][0]==pins['lean_bin'] and all(x in c['argv'] for x in ['-j1','-M3500','-DwarningAsError=true']) and k['argv']==[pins['leanchecker_bin'],module]
 assert c['LEAN_PATH']==k['LEAN_PATH']==':'.join([str(F/'build')]+pins['upstream_lean_paths']) and c['LEAN_NUM_THREADS']==k['LEAN_NUM_THREADS']==1
 found=re.findall(r'depends on axioms: \[([^\]]*)\]',(F/'audit'/axf).read_text(errors='replace'));assert found,axf
 assert all({y.strip() for y in f.split(',')}<=trio for f in found),axf
 green.append(dict(module=module,source_sha256=source,olean_sha256=olean,compile=cl,checker=kl,axioms=axf,checkpoint=ckpt,compile_receipt_sha256=sha(F/(cl+'.receipt.json')),checker_receipt_sha256=sha(F/(kl+'.receipt.json'))))
gc=next(x for x in jsonrows(F/'r7_genuine_compile_043.output.txt') if x.get('stage')=='compile' and x.get('module')=='URMatchingGenuineCycle');gk=next(x for x in jsonrows(F/'r7_genuine_kernel_044.output.txt') if x.get('stage')=='check' and x.get('module')=='URMatchingGenuineCycle')
assert gc['exit']==0 and gk['exit']==1 and gc['source_sha256_after']==gk['source_sha256_after']==sha(F/'src/URMatchingGenuineCycle.lean') and 'Subwalks.olean.private' in json.dumps(read(F/'r7_genuine_kernel_044.receipt.json'))+(F/'r7_genuine_kernel_044.output.txt').read_text(errors='replace') and 'URMatchingGenuineCycle' not in result['strict_green_modules']
for q in F.glob('*.output.txt'):assert 'sorryAx' not in q.read_text(errors='replace'),q.name
allrows=base['immutable_green_modules']+green;assert len(allrows)==42
for row in allrows+[dict(module='URMatchingGenuineCycle')]:
 text=(F/'src'/(row['module']+'.lean')).read_text();assert not re.search(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|^\s*axiom\b',text,re.M),row['module']

rows=[];pat=re.compile(r"failed to read file '([^']+)'")
for lane in ['high-girth-ur-matching-formal-sol-r4','high-girth-ur-matching-formal-sol-r5','high-girth-ur-matching-formal-sol-r6','high-girth-ur-matching-formal-sol-r7','parking-strong-a2-formal-sol-r1']:
 for q in sorted((P/lane).glob('*.receipt.json')):
  rec=read(q)
  if rec['exit']==0:continue
  out=q.with_name(q.name[:-len('.receipt.json')]+'.output.txt');text=str(rec.get('stderr'))+(out.read_text(errors='replace') if out.exists() else '');m=pat.search(text)
  if m:rows.append(dict(lane=lane,label=q.name[:-len('.receipt.json')],file=m.group(1).split('/lean/')[-1],wall_s=rec.get('wall_s'),sampled_group_rss_peak_bytes=rec.get('sampled_group_rss_peak_bytes'),as_limit_bytes=rec.get('as_limit_bytes')))
assert rows and all(x['as_limit_bytes']==6*1024**3 for x in rows)
ev=dict(utc=now,count=len(rows),per_lane=dict(collections.Counter(x['lane'] for x in rows)),distinct_files=sorted({x['file'] for x in rows}),max_sampled_rss_bytes=max(x['sampled_group_rss_peak_bytes'] for x in rows),max_wall_s=max(x['wall_s'] for x in rows),rows=rows,root_hypothesis='leanchecker memory-maps every olean in the import closure, so RLIMIT_AS of 6 GiB may be exhausted by virtual mappings while real memory stays near 1 GiB. Inference from logs only; not directly tested. Root runs no Lean and raising the cap needs user authorization.',root_Lean_execution=False)
save(ROOT/'kernel-read-failure-evidence-r7.json',ev)

fs='338806 uncredited formal r7 INCOMPLETE, no literal negation, no paper, no technical PASS. Five new strict compile plus kernel green modules with scoped axioms verified byte/log/receipt on top of thirty-seven sealed baseline modules, forty-two in all: permutation-graph closed walks are even, every walk position has the expected bipartition parity, tail-nodup gives injective positions, and a left-started even tail-nodup closed walk yields distinct X and Y embeddings and an actual occurring coloured witness, so all short ordered-cycle vertices are deleted. URMatchingGenuineCycle, using actual Walk.IsCycle for left starts, strictly compiled but its kernel check exited 1 failing to read upstream Walk/Subwalks.olean.private, so it is NOT certified. Unpaid: genuine IsCycle extraction for both sides and complete short-cycle destruction, genuine girth and source conventions; induced first-colour matching and retained cardinal; transport of the obstruction to all survivor UR matchings and the strict real ratio; standard matching, degree, induce, universe, relabeling and coding bridges; universal literal negation; full audits, controls, empty-build replay, paper, independent review and root scientific adjudication. 818 manifest files, 667 frozen bindings, 42 modules verified; no root Lean execution. Scientific HOLD and credit 0 unchanged, 57/60.'
fr=dict(utc=now,mathdb_id=338806,source_lane=str(F),manifest_sha256=sha(F/'MANIFEST.json'),verified_manifest_files=818,verified_frozen_bindings=667,green_modules=allrows,new_green_modules=green,compiled_not_kernel_green=[dict(module='URMatchingGenuineCycle',compile='r7_genuine_compile_043',failed_checker='r7_genuine_kernel_044')],runner_receipts=frec,body_audit_unpaid=True,result=result,scientific_summary=fs,root_disposition='INCOMPLETE_UNCREDITED_FORMAL_RESEARCH_CONTINUE',credit=0,accepted_new=57,terminal_self_exclusions=fex,root_scope='Documentary integrity only; no Lean/math execution by root.')
den=read(ROOT/'inherited-denials-r538.json');den['utc']=now;den['root_highgirth338806_formal_r7_scope']=fs
save(P/'high-girth-ur-matching-formal-parent-integration-r7.json',fr);denpath=ROOT/'inherited-denials-r539.json';save(denpath,den)
save(ROOT/'formal-r7-intake-report.json',dict(utc=now,files=818,frozen=667,verified_green_modules=allrows,credit=0,accepted_new=57,no_root_mathematics=True))

L.mkdir();origins={}
def copy(src,rel):
 dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]=dict(path=str(src),sha256=sha(src))
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','model-policy-sol-only.json','PINS.json','formal_command.py','check.sh','checker.sh']:copy(F/h,h)
for h in ['check.sh','checker.sh']:(L/h).chmod(0o755)
for d in ['src','build','cache','audit','receipt','logs','results','cleanroom/src','cleanroom/build','manuscript','output/pdf']:(L/d).mkdir(parents=True,exist_ok=True)
for q in (F/'inputs').rglob('*'):
 if q.is_file():
  rel=Path('inputs')/q.relative_to(F/'inputs');s=str(rel)
  if s=='inputs/ROOT-AUTHORIZATION.json':rel=Path('inputs/PREVIOUS-ROOT-AUTHORIZATION-r7.json')
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
copy(F/'src/URMatchingGenuineCycle.lean','inputs/drafts-r7/URMatchingGenuineCycle.lean')
for q in sorted((F/'audit').iterdir()):
 if q.is_file():copy(q,'inputs/drafts-r7/audit/'+q.name)
labels={'r7_genuine_compile_043','r7_genuine_kernel_044'}
for row in green:labels.update([row['compile'],row['checker'],row['checkpoint']])
labels.update(n[:-len('.receipt.json')] for n in failures)
for label in sorted(labels):
 for suffix in ['.receipt.json','.output.txt']:copy(F/(label+suffix),'inputs/previous-receipts-r7/'+label+suffix)
for name in ['SUMMARY.md','CHECKPOINT.md','results/338806.json','source-to-literal-map.json']:
 if (F/name).is_file():copy(F/name,'inputs/previous-r7/'+Path(name).name)
save(L/'BASELINE.json',dict(origin=str(F),root_verified_manifest_sha256=sha(F/'MANIFEST.json'),immutable_green_modules=baseline,uncompiled_or_uncertified_drafts='inputs/drafts and inputs/drafts-r4 to inputs/drafts-r7 only; NOT paid theorem/source endpoint. URMatchingGenuineCycle strict compiled in R7 but is NOT kernel-certified.',rule='Own copied baseline source and all compiler sidecars are immutable; do not rewrite or recompile these in production. Import own-build sealed oleans. Final empty-build source-only replay must rebuild copied source plus new source with no production or legacy paths. No external origin paths may be followed.'))
authorization=dict(utc=now,mathdb_id=338806,status='CONTINUE_UNCOUNTED_FORMAL_RESEARCH_INCOMPLETE_SCIENTIFIC_HOLD_PRESERVED',authority='Continuation of existing user-authorized literal Lean research; latest user message: keep progress. No additional acceptance or scientific waiver.',previous_authorization=str(P/'high-girth-ur-matching-formal-research-authorization-r7.json'),basis='Root documentary verification confirms forty-two strict and kernel green modules and no literal endpoint. Continue the actual unpaid pipeline without repeating green baseline.',scientific_status='HOLD remains; final, prior and significance gates can veto credit. No source-access waiver implied by formal progress.',paid=[x['module'] for x in baseline],unpaid=result['unpaid'],credit=0,accepted_new=57,target_new=60,root_Lean_or_math_execution=False)
save(P/'high-girth-ur-matching-formal-research-authorization-r8.json',authorization);save(L/'inputs/ROOT-AUTHORIZATION.json',authorization)
peers=['expanded-corpus-r518','expanded-corpus-r519']
task=(F/'TASK.txt').read_text().replace(str(F),str(L)).replace('expanded-corpus-r516',peers[0]).replace('expanded-corpus-r517',peers[1])
override=f'''R8 CONTINUATION OVERRIDE. GPT-6.1 Sol HIGH/DEFAULT ONLY, no children, offline uncredited research. Scientific HOLD, credit 0 and 57 of 60 unchanged. This override supersedes the earlier R3 to R7 first-new-proof, base-writing and baseline-replay instructions in the inherited TASK below; every other source, model, cap, audit, replay and acceptance restriction remains. The full literal endpoint is still unpaid; do not stop at another helper or control milestone.

FIRST command EXACTLY: timeout 20 python3 -I -B {L}/bootstrap.py
SECOND command EXACTLY: timeout 140 python3 -I -B {L}/verify_frozen.py before
Then use only your own immutable capped runner, writer and wrappers. Active peers {peers[0]} and {peers[1]} are entirely protected, including metadata, stat, hash, list, glob, poll, reservations and flat integrations. R3 to R7 and all other lanes are now external and protected, even baseline origin paths: your own copies only, plus pinned upstream APIs. No network, source queries, git, install, accounts, browser, other models, mathematical programs, solvers, shared or tmp writes, or background jobs. PINS, helpers and baseline are frozen and never overwritten.

Read BASELINE.json, inputs/ROOT-AUTHORIZATION.json, inputs/previous-r7/CHECKPOINT.md, inputs/previous-r7/338806.json, and selected receipts and the author and independent proofs. The FORTY-TWO baseline modules listed in BASELINE.json and every own-build compiler sidecar are IMMUTABLE; root verified their actual strict compile and checker hashes and receipts. Do not rewrite or recompile them unchanged and do not run check.sh on these names. The final cleanroom replay must freshly build ALL baseline SOURCE plus new modules from an empty own build with upstream only and no production, legacy or author paths. If a genuine baseline fidelity error arises, disclose it precisely and add new faithful definitions or proved generic bridges without mutating the frozen baseline or assuming the endpoint.

FIRST NEW-PROOF work after the mandatory read and pin check must advance the first UNPAID real item below, with an immediate strict compile and kernel check, before broad API or planning tours. Follow the copied complete independent PROOF, not an invented weakened question. Work in this order, which puts first the items that do not need the blocked upstream Walk files:
1. The induced survivor first-colour matching and its retained cardinal greater than 99N/100, using that the first colour loses at most one edge per deleted vertex.
2. Transport of the no-hole obstruction to all actual survivor UR matchings through URMatching.ur_partition_empty_rectangle, and the strict real ratio.
3. Standard subgraph matching and matching-number correspondence, the standard all-vertex degree correspondence, and the generic induced graph to standard induce correspondence, with light imports.
4. Genuine Walk.IsCycle extraction for both starting sides, complete destruction of all short survivor cycles, genuine girth, and forest and source conventions. inputs/drafts-r7/URMatchingGenuineCycle.lean compiled for left starts, but its kernel check exited 1 failing to read upstream Walk/Subwalks.olean.private. Earlier in R7 a parity module was repaired by replacing a Paths import with Walk.Basic. Try one genuinely changed lighter import graph if a plausible one exists; if the checker still cannot read upstream files, keep the source, record the exact failure and move on. Do not loop on this item.
5. Finite-type, universe, relabeling and canonical-coding bridges and the universal literal negation.
A module that compiles but fails its kernel check is NOT certified and may not be reported as green. No assumed good tuple, no holes, expander, probability existence, conclusion-bearing premise or finite enumeration encoding the answer. Existing green modules are not the endpoint.

Across R4 to R7, import-heavy modules hit unreadable upstream oleans, bad_alloc and failed-to-create-thread errors, and those were repaired only by changed import graphs, simplification or splitting. Use minimal imports and small modules and never retry unchanged. No cap or limit increase is authorized in this lane. Every Lean or audit process uses -j1, -M3500 or stricter, LEAN_NUM_THREADS 1 and the same AS 6GiB, RSS 6GiB and CPU 115 caps. Preserve every failure with its true exit. Every new green module needs compile, checker, scoped axioms and a checkpoint with exact source, olean, log and receipt hashes, with no future-tense handback. Keep results/338806.json strict_green_modules complete. If interrupted, persist actual new mathematical sources, the last real diagnostics and a precise unpaid ledger.

The manuscript, PDF, full body audits, controls, full source-only replay, source-fidelity review, independent review and root scientific adjudication are unpaid. No paper exists; make no misleading reuse claim. Scientific HOLD must stay explicit in results and any manuscript. Source 1803.11032 and final DOI 10.1007/s00373-018-1991-8 are closed to new deliveries. A final technical PASS comes only after the actual endpoint, all bridges, replay and audits; acceptance and credit are root-only and may be refused. Seal standalone frozen-after, then an exhaustive own-byte manifest including baseline sidecars, new sources, all completed receipts, inputs, audits and any paper, with exact terminal noncircular exclusions. Credit 0, 57 of 60 unchanged.

INHERITED FULL TASK (the override above controls all conflicts):
'''
(L/'TASK.txt').write_text(override+task)
save(L/'INPUT-ORIGINS.json',origins);save(L/'ROOT-PREP.json',dict(utc=now,lane=str(L),mathdb_id=338806,model='gpt-6.1-sol',reasoning='high',service='default',scientific_hold=True,credit=0,accepted_new=57,children=False,network=False,root_math_or_Lean_execution=False,protected_peers=peers))
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=338806,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),baseline_modules=len(baseline),model='gpt-6.1-sol',reasoning='high',service='default',credit=0,accepted_new=57,scientific_hold=True,protected_peers=peers)
save(ROOT/'high-girth-ur-matching-formal-r8-ready.json',ready);save(ROOT/'selection-routing-high-girth-ur-matching-formal-r8.json',dict(ids=[338806],sources=['https://arxiv.org/abs/1803.11032'],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
print(json.dumps(dict(r7_manifest=818,frozen=667,green=len(allrows),kernel_read_evidence=dict(count=ev['count'],per_lane=ev['per_lane'],distinct=len(ev['distinct_files']),max_rss=ev['max_sampled_rss_bytes'],max_wall=ev['max_wall_s']),r8=ready,credit=0,accepted_new=57)))
