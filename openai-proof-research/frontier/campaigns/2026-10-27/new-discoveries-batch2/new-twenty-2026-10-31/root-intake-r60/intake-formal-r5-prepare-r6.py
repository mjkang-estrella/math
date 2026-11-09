"""Root documentary verification of 338806 formal r5 and preparation of the sealed-baseline r6 continuation; no root mathematics or Lean execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
F=P/'high-girth-ur-matching-formal-sol-r5';L=P/'high-girth-ur-matching-formal-sol-r6';assert not L.exists()
def jsonrows(q):
 out=[]
 for line in q.read_text(errors='replace').splitlines():
  try:v=json.loads(line)
  except ValueError:continue
  if isinstance(v,dict):out.append(v)
 return out

# Every documentary check precedes any root mutation.
m=read(F/'MANIFEST.json');assert len(m['files'])==588 and m['credit']==0 and m['scientific_status']=='HOLD'
names=set()
for n,x in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=F/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
fex=m['terminal_noncircular_exclusions'];assert set(fex)=={'MANIFEST.json','r5_terminal_manifest_079.receipt.json','r5_terminal_manifest_079.output.txt'}
inventory=set()
for q in F.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(F)))
assert inventory==names|set(fex)
frozen(F,336)
assert sha(F/'TASK.txt')==read(ROOT/'high-girth-ur-matching-formal-r5-ready.json')['task_sha256']
failures={n+'.receipt.json':1 for n in ['r5_read_inputs_001','r5_product_compile_005','r5_product_compile_007','r5_count_api_011','r5_fibers_compile_016','r5_fibers_compile_018','r5_fibers_kernel_019','r5_exact_compile_027','r5_bound_compile_032','r5_bound_kernel_036','r5_bound_reduced_kernel_042','r5_strict_compile_044','r5_bound_minimal_compile_048','r5_bound_natprod_compile_050','r5_nohole_compile_057','r5_union_nat_compile_059','r5_prescription_compile_066','r5_descriptions_compile_071']}
frec=receipts(F,failures);assert read(F/'r5_terminal_manifest_079.receipt.json')['exit']==0
pins=read(F/'PINS.json');result=read(F/'results/338806.json');base=read(F/'BASELINE.json')
assert result['formal_status']=='INCOMPLETE_NO_LITERAL_ENDPOINT' and result['credit']==0 and result['scientific_status']=='HOLD' and result['technical_pass'] is False
for row in base['immutable_green_modules']:assert sha(F/'src'/(row['module']+'.lean'))==row['source_sha256'] and sha(F/'build'/(row['module']+'.olean'))==row['olean_sha256']
assert len(base['immutable_green_modules'])==18
new=['URMatchingAvoidanceProduct','URMatchingPermutationFibers','URMatchingAvoidanceCount','URMatchingAvoidanceBound','URMatchingHoleUnion','URMatchingPrescriptions','URMatchingCycleDescriptions']
rowsby=collections.defaultdict(list)
for q in sorted(F.glob('r5_*.output.txt')):
 label=q.name[:-len('.output.txt')]
 for v in jsonrows(q):
  if v.get('stage') in('compile','check') and v.get('module'):rowsby[v['module']].append((label,v))
trio={'propext','Classical.choice','Quot.sound'};green=[]
for module in new:
 assert module in json.dumps(result),module
 source=sha(F/'src'/(module+'.lean'));olean=sha(F/'build'/(module+'.olean'))
 cs=[(l,v) for l,v in rowsby[module] if v['stage']=='compile' and v['exit']==0 and v['source_sha256_after']==source and v['olean_sha256_after']==olean]
 ks=[(l,v) for l,v in rowsby[module] if v['stage']=='check' and v['exit']==0 and v['source_sha256_after']==source and v['olean_sha256_after']==olean]
 assert len(cs)==1 and len(ks)==1,(module,cs,ks)
 cl,c=cs[0];kl,k=ks[0]
 assert read(F/(cl+'.receipt.json'))['exit']==read(F/(kl+'.receipt.json'))['exit']==0
 assert c['source_sha256_before']==c['source_sha256_after']==k['source_sha256_before']==k['source_sha256_after']==source and k['olean_sha256_before']==k['olean_sha256_after']==olean
 assert c['argv'][0]==pins['lean_bin'] and all(x in c['argv'] for x in ['-j1','-M3500','-DwarningAsError=true']) and k['argv']==[pins['leanchecker_bin'],module]
 assert c['LEAN_PATH']==k['LEAN_PATH']==':'.join([str(F/'build')]+pins['upstream_lean_paths']) and c['LEAN_NUM_THREADS']==k['LEAN_NUM_THREADS']==1
 ax=module+'Axioms';axsource=sha(F/'src'/(ax+'.lean'));hits=[(l,v) for l,v in rowsby[ax] if v['stage']=='compile' and v['exit']==0 and v['source_sha256_after']==axsource]
 assert hits,ax
 found=re.findall(r'depends on axioms: \[([^\]]*)\]',(F/(hits[-1][0]+'.output.txt')).read_text(errors='replace'));assert found,ax
 assert all({y.strip() for y in f.split(',')}<=trio for f in found),ax
 green.append(dict(module=module,source_sha256=source,olean_sha256=olean,compile=cl,checker=kl,axioms=hits[-1][0],compile_receipt_sha256=sha(F/(cl+'.receipt.json')),checker_receipt_sha256=sha(F/(kl+'.receipt.json'))))
for q in F.glob('r5_*.output.txt'):assert 'sorryAx' not in q.read_text(errors='replace'),q.name
allrows=base['immutable_green_modules']+green;assert len(allrows)==25
for row in allrows:
 text=(F/'src'/(row['module']+'.lean')).read_text();assert not re.search(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|^\s*axiom\b',text,re.M),row['module']
fs='338806 uncredited formal r5 INCOMPLETE, no literal negation, no paper, no technical PASS. Seven new strict compile plus kernel green modules verified byte/log/receipt on top of eighteen sealed baseline modules, twenty-five in all: the exact one-colour avoidance count (N-|B|).descFactorial |A| * (N-|A|)! via restriction fibers and injection counting; the natural geometric bound for actual permutations and the full 100-permutation tuple space; the integer union bound over all a-square rectangles on 4a labels and, for every a>0, four times the bad-hole count strictly below the size of the tuple space, hence an actual no-hole tuple with no short-cycle property asserted; exact independent per-colour injective-prescription counts and conflict zero counts; and ordered coloured-cycle descriptions with their enumeration bound. Unpaid: conversion of witnesses to per-colour partial maps, distinct prescribed edges, the individual witness probability and first moment; finite Markov and union existence for every girth; induced survivor, degree, no-hole, girth, relabeling and matching transport; matching, source and universe bridges; strict real ratio and universal literal negation; full audits, controls, empty-build replay, paper, independent review and root scientific adjudication. Bookkeeping limit: results/338806.json strict_green_modules still lists only the eighteen baseline names, so root verified the seven new modules directly from receipts. Kernel failures from unreadable upstream private oleans (Omega, GroupWithZero/InjSurj) were repaired only by changed import graphs. 588 manifest files, 336 frozen bindings, 25 modules verified; no root Lean execution. Scientific HOLD and credit 0 unchanged, 57/60.'
fr=dict(utc=now,mathdb_id=338806,source_lane=str(F),manifest_sha256=sha(F/'MANIFEST.json'),verified_manifest_files=588,verified_frozen_bindings=336,green_modules=allrows,new_green_modules=green,runner_receipts=frec,body_audit_unpaid=True,result=result,scientific_summary=fs,root_disposition='INCOMPLETE_UNCREDITED_FORMAL_RESEARCH_CONTINUE',credit=0,accepted_new=57,terminal_self_exclusions=fex,root_scope='Documentary integrity only; no Lean/math execution by root.')
den=read(ROOT/'inherited-denials-r531.json');den['utc']=now;den['root_highgirth338806_formal_r5_scope']=fs
save(P/'high-girth-ur-matching-formal-parent-integration-r5.json',fr);denpath=ROOT/'inherited-denials-r532.json';save(denpath,den)
save(ROOT/'formal-r5-intake-report.json',dict(utc=now,files=588,frozen=336,verified_green_modules=allrows,credit=0,accepted_new=57,no_root_mathematics=True))

L.mkdir();origins={}
def copy(src,rel):
 dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]=dict(path=str(src),sha256=sha(src))
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','model-policy-sol-only.json','PINS.json','formal_command.py','check.sh','checker.sh']:copy(F/h,h)
for h in ['check.sh','checker.sh']:(L/h).chmod(0o755)
for d in ['src','build','cache','audit','receipt','logs','results','cleanroom/src','cleanroom/build','manuscript','output/pdf']:(L/d).mkdir(parents=True,exist_ok=True)
for q in (F/'inputs').rglob('*'):
 if q.is_file():
  rel=Path('inputs')/q.relative_to(F/'inputs');s=str(rel)
  if s=='inputs/ROOT-AUTHORIZATION.json':rel=Path('inputs/PREVIOUS-ROOT-AUTHORIZATION-r5.json')
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
for q in sorted((F/'src').glob('*Axioms.lean')):copy(q,'inputs/drafts-r5/'+q.name)
labels={next(F.glob('r5_*_003.receipt.json')).name[:-len('.receipt.json')]}
for row in green:labels.update([row['compile'],row['checker'],row['axioms']])
labels.update(n[:-len('.receipt.json')] for n in failures)
for label in sorted(labels):
 for suffix in ['.receipt.json','.output.txt']:copy(F/(label+suffix),'inputs/previous-receipts-r5/'+label+suffix)
for name in ['SUMMARY.md','CHECKPOINT.md','results/338806.json']:copy(F/name,'inputs/previous-r5/'+Path(name).name)
save(L/'BASELINE.json',dict(origin=str(F),root_verified_manifest_sha256=sha(F/'MANIFEST.json'),immutable_green_modules=baseline,uncompiled_or_uncertified_drafts='inputs/drafts, inputs/drafts-r4 and inputs/drafts-r5 only; NOT paid theorem/source endpoint',rule='Own copied baseline source and all compiler sidecars are immutable; do not rewrite or recompile these in production. Import own-build sealed oleans. Final empty-build source-only replay must rebuild copied source plus new source with no production or legacy paths. No external origin paths may be followed.'))
authorization=dict(utc=now,mathdb_id=338806,status='CONTINUE_UNCOUNTED_FORMAL_RESEARCH_INCOMPLETE_SCIENTIFIC_HOLD_PRESERVED',authority='Continuation of existing user-authorized literal Lean research; latest user message: keep progress. No additional acceptance or scientific waiver.',previous_authorization=str(P/'high-girth-ur-matching-formal-research-authorization-r5.json'),basis='Root documentary verification confirms twenty-five strict and kernel green modules and no literal endpoint. Continue the actual unpaid pipeline without repeating green baseline.',scientific_status='HOLD remains; final, prior and significance gates can veto credit. No source-access waiver implied by formal progress.',paid=[x['module'] for x in baseline],unpaid=result['unpaid'],credit=0,accepted_new=57,target_new=60,root_Lean_or_math_execution=False)
save(P/'high-girth-ur-matching-formal-research-authorization-r6.json',authorization);save(L/'inputs/ROOT-AUTHORIZATION.json',authorization)
peers=['expanded-corpus-r515','parking-strong-a2-formal-sol-r1']
task=(F/'TASK.txt').read_text().replace(str(F),str(L)).replace('nfm-dirichlet-psd-source-review-sol-r1',peers[0]).replace('parking-strong-a2-source-review-sol-r1',peers[1])
override=f'''R6 CONTINUATION OVERRIDE. GPT-6.1 Sol HIGH/DEFAULT ONLY, no children, offline uncredited research. Scientific HOLD, credit 0 and 57 of 60 unchanged. This override supersedes the earlier R3, R4 and R5 first-new-proof, base-writing and baseline-replay instructions in the inherited TASK below; every other source, model, cap, audit, replay and acceptance restriction remains. The full literal endpoint is still unpaid; do not stop at another helper or control milestone.

FIRST command EXACTLY: timeout 20 python3 -I -B {L}/bootstrap.py
SECOND command EXACTLY: timeout 140 python3 -I -B {L}/verify_frozen.py before
Then use only your own immutable capped runner, writer and wrappers. Active peers {peers[0]} and {peers[1]} are entirely protected, including metadata, stat, hash, list, glob, poll, reservations and flat integrations. R3, R4, R5 and all other lanes are now external and protected, even baseline origin paths: your own copies only, plus pinned upstream APIs. No network, source queries, git, install, accounts, browser, other models, mathematical programs, solvers, shared or tmp writes, or background jobs. PINS, helpers and baseline are frozen and never overwritten.

Read BASELINE.json, inputs/ROOT-AUTHORIZATION.json, inputs/previous-r5/CHECKPOINT.md and inputs/previous-r5/338806.json, the copied source-to-literal map, and selected receipts and the author and independent proofs. The TWENTY-FIVE baseline modules listed in BASELINE.json and every own-build compiler sidecar are IMMUTABLE; root verified their actual strict compile and checker hashes and receipts. Do not rewrite or recompile them unchanged and do not run check.sh on these names. The final cleanroom replay must freshly build ALL baseline SOURCE plus new modules from an empty own build with upstream only and no production, legacy or author paths. If a genuine baseline fidelity error arises, disclose it precisely and add new faithful definitions or proved generic bridges without mutating the frozen baseline or assuming the endpoint.

FIRST NEW-PROOF work after the mandatory read and pin check must advance the first UNPAID real item below, with an immediate strict compile and kernel check, before broad API or planning tours. Follow the copied complete independent PROOF, not an invented weakened question. Work in ordinary proof order:
1. Convert every actual coloured short-cycle and parallel witness (URMatchingCycleDescriptions) into its per-colour partial maps, prove the total number of distinct prescribed edges, the individual witness probability bound using URMatchingPrescriptions, and the summed first-moment bound. Inconsistent prescriptions have probability 0.
2. Finite Markov and union existence of an actual tuple for every girth at fixed degree 100, jointly with the no-hole estimate already certified in URMatchingHoleUnion. The existing no-hole tuple asserts no short-cycle property.
3. The induced survivor construction: simplicity, degree, no holes, genuine cycle and girth transport, relabeling and matching retention. The existing Deletion module covers only original-graph lost-edge cardinality.
4. Standard subgraph matching and matching-number correspondence, the standard all-vertex degree bridge, genuine Walk.IsCycle, forest and source conventions, and finite-type, universe, relabeling and canonical-coding bridges.
5. The strict real ratio and the universal literal negation.
No assumed good tuple, no holes, expander, probability existence, conclusion-bearing premise or finite enumeration encoding the answer. Existing green modules are not the endpoint.

inputs/drafts-r4/URMatchingSource.lean is an input only and NOT certified: its R4 kernel check exited 1 on an unreadable upstream Cardinal/Finite.olean.private. In R5, kernel checks also failed on unreadable upstream Omega and GroupWithZero/InjSurj private oleans, and those were repaired only by removing heavy imports and proving natural-number estimates locally. So use minimal imports and small modules, certify source conventions through a changed import graph or genuinely repaired source, and never retry unchanged. No cap or limit increase. Every Lean or audit process uses -j1, -M3500 or stricter, LEAN_NUM_THREADS 1 and the same AS 6GiB, RSS 6GiB and CPU 115 caps. Preserve every failure with its true exit. Every new green module needs compile, checker, scoped axioms and a checkpoint with exact source, olean, log and receipt hashes, with no future-tense handback. Keep results/338806.json strict_green_modules complete: R5 left it listing only eighteen names. If interrupted, persist actual new mathematical sources, the last real diagnostics and a precise unpaid ledger.

The manuscript, PDF, full body audits, controls, full source-only replay, source-fidelity review, independent review and root scientific adjudication are unpaid. No paper exists; make no misleading reuse claim. Scientific HOLD must stay explicit in results and any manuscript. Source 1803.11032 and final DOI 10.1007/s00373-018-1991-8 are closed to new deliveries. A final technical PASS comes only after the actual endpoint, all bridges, replay and audits; acceptance and credit are root-only and may be refused. Seal standalone frozen-after, then an exhaustive own-byte manifest including baseline sidecars, new sources, all completed receipts, inputs, audits and any paper, with exact terminal noncircular exclusions. Credit 0, 57 of 60 unchanged.

INHERITED FULL TASK (the override above controls all conflicts):
'''
(L/'TASK.txt').write_text(override+task)
save(L/'INPUT-ORIGINS.json',origins);save(L/'ROOT-PREP.json',dict(utc=now,lane=str(L),mathdb_id=338806,model='gpt-6.1-sol',reasoning='high',service='default',scientific_hold=True,credit=0,accepted_new=57,children=False,network=False,root_math_or_Lean_execution=False,protected_peers=peers))
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=338806,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),baseline_modules=len(baseline),model='gpt-6.1-sol',reasoning='high',service='default',credit=0,accepted_new=57,scientific_hold=True,protected_peers=peers)
save(ROOT/'high-girth-ur-matching-formal-r6-ready.json',ready);save(ROOT/'selection-routing-high-girth-ur-matching-formal-r6.json',dict(ids=[338806],sources=['https://arxiv.org/abs/1803.11032'],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
print(json.dumps(dict(r5_manifest=588,frozen=336,green=len(allrows),new=[x['module'] for x in green],r6=ready,credit=0,accepted_new=57)))
