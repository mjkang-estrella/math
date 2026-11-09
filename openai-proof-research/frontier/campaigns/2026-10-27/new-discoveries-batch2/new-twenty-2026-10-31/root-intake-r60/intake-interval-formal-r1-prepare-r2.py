"""Root documentary verification of 336276 formal r1 and preparation of a finite-only sealed-baseline r2 continuation; no root mathematics or Lean execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
F=P/'interval-kwidth-formal-sol-r1';L=P/'interval-kwidth-formal-sol-r2';assert not L.exists()
def jsonrows(q):
 out=[]
 for line in q.read_text(errors='replace').splitlines():
  try:v=json.loads(line)
  except ValueError:continue
  if isinstance(v,dict):out.append(v)
 return out

# Every documentary check precedes any root mutation.
fex=manifest(F,'OWN-MANIFEST.json',325,'manifest_seal92','terminal_noncircular_exclusions');frozen(F,35)
assert sha(F/'TASK.txt')==read(ROOT/'interval-kwidth-formal-r1-ready.json')['task_sha256']
failures={n+'.receipt.json':1 for n in ['base_kernel06','base_stack_compile08','base_fix09','base_stack_kernel10','minimum_compile18','partition_compile25','dummy_compile34','hall_compile38','hall_full_compile42','hall_full_fix43','hall_full_fix44','hall_full_kernel45','deficiency_compile49','deficiency_fix51','threshold_compile56','suffix_compile60','sampling_kernel74','sampling_min_kernel77','literal_kernel80','audit_controls84','cleanroom87']}
failures['base_compile05.receipt.json']=250;failures['base_kernel12.receipt.json']=250
frec=receipts(F,failures);assert read(F/'manifest_seal92.receipt.json')['exit']==0 and read(F/'cleanroom_fixed90.receipt.json')['exit']==0
pins=read(F/'PINS.json');result=read(F/'results/336276.json')
assert result['credit']==0 and result['status']=='INCOMPLETE_HAND_BACK_ZERO_CREDIT' and result['literal_endpoint_proved'] is False and result['full_transitive_audit_pass'] is False and result['compile_only_uncertified_modules']==['IntervalSampling','IntervalLiteral']
pairs=[('IntervalBase','base_min15','base_min_kernel16'),('IntervalMinimum','minimum_fix19','minimum_kernel20'),('IntervalForest','forest_compile22','forest_kernel23'),('IntervalPartition','partition_fix26','partition_kernel27'),('IntervalMatching','matching_compile30','matching_kernel31'),('IntervalDummy','dummy_fix35','dummy_kernel36'),('IntervalHallUpper','hall_fix39','hall_kernel40'),('IntervalHall','hall_full_fix46','hall_full_kernel47'),('IntervalDeficiency','deficiency_fix53','deficiency_kernel54'),('IntervalThreshold','threshold_fix57','threshold_kernel58'),('IntervalSuffix','suffix_fix61','suffix_kernel62'),('IntervalEnvelope','envelope_compile64','envelope_kernel65'),('IntervalControls','controls_compile68','controls_kernel69')]
assert [p[0] for p in pairs]==result['strict_green_modules']
green=[]
for module,cl,kl in pairs:
 c=next(x for x in jsonrows(F/(cl+'.output.txt')) if x.get('stage')=='compile' and x.get('module')==module)
 k=next(x for x in jsonrows(F/(kl+'.output.txt')) if x.get('stage')=='check' and x.get('module')==module)
 assert c['exit']==k['exit']==read(F/(cl+'.receipt.json'))['exit']==read(F/(kl+'.receipt.json'))['exit']==0
 source=sha(F/'src'/(module+'.lean'));olean=sha(F/'build'/(module+'.olean'))
 assert c['source_sha256_before']==c['source_sha256_after']==k['source_sha256_before']==k['source_sha256_after']==source and c['olean_sha256_after']==k['olean_sha256_before']==k['olean_sha256_after']==olean
 assert c['argv'][0]==pins['lean_bin'] and all(x in c['argv'] for x in ['-j1','-M3500','-DwarningAsError=true','-s8192']) and k['argv']==[pins['leanchecker_bin'],module]
 assert c['LEAN_PATH']==k['LEAN_PATH']==':'.join([str(F/'build')]+pins['upstream_lean_paths']) and c['LEAN_NUM_THREADS']==k['LEAN_NUM_THREADS']==1
 green.append(dict(module=module,source_sha256=source,olean_sha256=olean,compile=cl,checker=kl,compile_receipt_sha256=sha(F/(cl+'.receipt.json')),checker_receipt_sha256=sha(F/(kl+'.receipt.json'))))
found=re.findall(r'depends on axioms: \[([^\]]*)\]',(F/'audit_fix86.output.txt').read_text());assert found and all({y.strip() for y in f.split(',')}<={'propext','Classical.choice','Quot.sound'} for f in found)
for q in F.glob('*.output.txt'):assert 'sorryAx' not in q.read_text(errors='replace'),q.name
for q in (F/'src').glob('*.lean'):assert not re.search(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|^\s*axiom\b',q.read_text(),re.M),q.name
for f,lab in [('IntervalSampling','sampling_min_kernel77'),('IntervalLiteral','literal_kernel80')]:
 assert 'failed to read file' in (F/(lab+'.output.txt')).read_text(errors='replace')+str(read(F/(lab+'.receipt.json')).get('stderr'))
assert sha(F/'stack_driver.py')=='4ab81c959a136e808b72270aa85e2d25177a7ffc19bf7a18b9dddc58195f99ac'

pat=re.compile(r"failed to read file '[^']+'|failed to create thread|bad_alloc|INTERNAL PANIC: out of memory");lane_rows=[]
for q in sorted(F.glob('*.receipt.json')):
 rec=read(q)
 if rec['exit']==0:continue
 out=q.with_name(q.name[:-len('.receipt.json')]+'.output.txt');text=str(rec.get('stderr'))+(out.read_text(errors='replace') if out.exists() else '');mm=pat.search(text)
 if mm:lane_rows.append(dict(label=q.name[:-len('.receipt.json')],kind='read_failure' if 'read file' in mm.group(0) else mm.group(0),sampled_group_rss_peak_bytes=rec.get('sampled_group_rss_peak_bytes')))
prior=read(ROOT/'kernel-read-failure-evidence-r8.json');ev=dict(utc=now,count=prior['count']+len(lane_rows),lanes=len(prior['per_lane'])+1,interval_r1_rows=lane_rows,max_sampled_rss_bytes=max([prior['max_sampled_rss_bytes']]+[x['sampled_group_rss_peak_bytes'] for x in lane_rows]),prior_evidence=str(ROOT/'kernel-read-failure-evidence-r8.json'),root_hypothesis=prior['root_hypothesis'],root_Lean_execution=False)
save(ROOT/'kernel-read-failure-evidence-interval-r1.json',ev)

fs='336276 formal r1 INCOMPLETE, credit 0, no literal endpoint, no paper. Thirteen finite modules are strict compile plus kernel green, verified byte/log/receipt, and passed a fresh source-only empty-build replay: tree-based width as an attained minimum over actual rooted chronological k-ary tree partitions, forest equivalence, the attained copy-matching optimum, the full k-fold Hall maximum-deficiency identity, the deterministic threshold lower bound, ancestor order for valid intervals, actual suffix maxima, later-block neighbour and envelope inclusions, and finite controls. IntervalSampling (two import graphs) and IntervalLiteral compile but fail kernel checks with failed to read file on upstream oleans, including Module/LinearMap/Defs, so the probability layer and literal expectation are NOT certified. Unpaid: balanced blocks and inequality (E), finite-grid envelope, Bernoulli variance, sampling, measurability, marginal CDFs, expectation inequality, the limit, full endpoint audit and wrong-constant controls, paper, independent review and root adjudication. Disclosed: the lane used a hash-pinned stack driver adding -s8192 with a 512 KiB stack rlimit, as its task permitted; all other flags and caps were retained. 325 manifest files, 35 frozen bindings, 13 modules verified; no root Lean execution. Prospective scientific pass unchanged, credit 0, 57/60.'
fr=dict(utc=now,mathdb_id=336276,source_lane=str(F),manifest_sha256=sha(F/'OWN-MANIFEST.json'),verified_manifest_files=325,verified_frozen_bindings=35,green_modules=green,compiled_not_kernel_green=['IntervalSampling','IntervalLiteral'],source_only_replay_receipt_sha256=sha(F/'cleanroom_fixed90.receipt.json'),runner_receipts=frec,result=result,scientific_summary=fs,root_disposition='INCOMPLETE_FORMAL_RESEARCH_FINITE_CONTINUATION',credit=0,accepted_new=57,terminal_self_exclusions=sorted(fex),root_scope='Documentary integrity only; no Lean/math execution by root.')
den=read(ROOT/'inherited-denials-r546.json');den['utc']=now;den['root_interval336276_formal_r1_scope']=fs
save(P/'interval-kwidth-formal-parent-integration-r1.json',fr);denpath=ROOT/'inherited-denials-r547.json';save(denpath,den)

L.mkdir();origins={}
def copy(src,rel):
 dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]=dict(path=str(src),sha256=sha(src))
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','model-policy-sol-only.json','PINS.json','formal_command.py','check.sh','checker.sh','stack_driver.py','replay_driver.py']:copy(F/h,h)
for h in ['check.sh','checker.sh']:(L/h).chmod(0o755)
for d in ['src','build','cache','audit','receipt','logs','results','cleanroom/src','cleanroom/build','manuscript','output/pdf']:(L/d).mkdir(parents=True,exist_ok=True)
for q in (F/'inputs').rglob('*'):
 if q.is_file():
  rel=Path('inputs')/q.relative_to(F/'inputs');s=str(rel)
  if s=='inputs/ROOT-AUTHORIZATION.json':rel=Path('inputs/PREVIOUS-ROOT-AUTHORIZATION-r1.json')
  elif s=='inputs/INHERITED-DENIALS.json':continue
  copy(q,str(rel))
copy(denpath,'inputs/INHERITED-DENIALS.json')
baseline=[]
for row in green:
 module=row['module'];copy(F/'src'/(module+'.lean'),'src/'+module+'.lean')
 blobs=[]
 for q in (F/'build').glob(module+'.*'):
  if q.is_file():copy(q,'build/'+q.name);blobs.append(dict(path='build/'+q.name,sha256=sha(q)))
 assert sha(L/'src'/(module+'.lean'))==row['source_sha256'] and sha(L/'build'/(module+'.olean'))==row['olean_sha256']
 baseline.append(dict(row,blobs=blobs))
for n in ['IntervalSampling.lean','IntervalLiteral.lean']:copy(F/'src'/n,'inputs/drafts-r1/'+n)
for q in sorted((F/'audit').iterdir()):
 if q.is_file():copy(q,'inputs/previous-r1/audit/'+q.name)
labels={'cleanroom_fixed90','audit_fix86','audit_run83','sampling_min76','literal_compile79'}
for row in green:labels.update([row['compile'],row['checker']])
labels.update(n[:-len('.receipt.json')] for n in failures)
for label in sorted(labels):
 for suffix in ['.receipt.json','.output.txt']:copy(F/(label+suffix),'inputs/previous-receipts-r1/'+label+suffix)
for name in ['SUMMARY.md','CHECKPOINT.md','results/336276.json','source-to-literal.json']:copy(F/name,'inputs/previous-r1/'+Path(name).name)
save(L/'BASELINE.json',dict(origin=str(F),root_verified_manifest_sha256=sha(F/'OWN-MANIFEST.json'),immutable_green_modules=baseline,uncompiled_or_uncertified_drafts='inputs/drafts-r1 only; IntervalSampling and IntervalLiteral are NOT kernel-certified',rule='Own copied baseline source and all compiler sidecars are immutable; do not rewrite or recompile these in production. Import own-build sealed oleans. Final empty-build source-only replay must rebuild copied source plus new source with no production or legacy paths. No external origin paths may be followed.'))
authorization=dict(utc=now,mathdb_id=336276,status='CONTINUE_FORMAL_RESEARCH_FINITE_ONLY_PROSPECTIVE_SCIENTIFIC_PASS_ACCEPTANCE_CLOSED',authority='Continuation of existing literal Lean research; latest user message: keep progress. No acceptance or waiver.',previous_authorization=str(P/'interval-kwidth-formal-research-authorization-r1.json'),basis='Root documentary verification confirms thirteen strict and kernel green finite modules and a source-only replay. Finite work remains below the kernel-check wall.',scope='Finite deterministic items only until the resource decision is made.',paid=[x['module'] for x in baseline],unpaid=result['unpaid'],credit=0,accepted_new=57,target_new=60,root_Lean_or_math_execution=False)
save(P/'interval-kwidth-formal-research-authorization-r2.json',authorization);save(L/'inputs/ROOT-AUTHORIZATION.json',authorization)
peers=['expanded-corpus-r520','expanded-corpus-r521']
task=(F/'TASK.txt').read_text().replace(str(F),str(L)).replace('high-girth-ur-matching-formal-sol-r8',peers[0]).replace('simplex-three-design-source-review-sol-r1',peers[1])
override=f'''R2 CONTINUATION OVERRIDE, FINITE ITEMS ONLY. GPT-6.1 Sol HIGH/DEFAULT ONLY, no children, offline research. Credit 0, prospective scientific pass, 57 of 60 unchanged. This override supersedes the earlier R1 first-new-proof and sequencing instructions in the inherited TASK below; every other source, model, cap, audit, replay and acceptance restriction remains.

FIRST command EXACTLY: timeout 20 python3 -I -B {L}/bootstrap.py
SECOND command EXACTLY: timeout 140 python3 -I -B {L}/verify_frozen.py before
Then use only your own immutable capped runner, writer, wrappers and the hash-pinned stack_driver.py and replay_driver.py. Run stack_driver.py the way R1 did, under run.py with FORMAL_OPERATION and FORMAL_MODULE set; it adds only -s8192 and a smaller stack rlimit, and every other flag and cap is retained. Active peers {peers[0]} and {peers[1]} are entirely protected, including metadata, stat, hash, list, glob, poll, reservations and flat integrations. R1 and all other lanes are now external and protected: your own copies only, plus pinned upstream APIs. No network, source queries, git, install, accounts, browser, other models, mathematical programs, solvers, shared or tmp writes, or background jobs. PINS, helpers and baseline are frozen.

Read BASELINE.json, inputs/ROOT-AUTHORIZATION.json, inputs/previous-r1/CHECKPOINT.md and 336276.json, inputs/review-r1/PROOF.md. The THIRTEEN baseline modules and all own-build sidecars are IMMUTABLE; do not rewrite or recompile them unchanged.

SCOPE OF THIS ROUND. Do only the finite deterministic items that sit below the kernel-check wall, then stop:
1. Balanced consecutive blocks with sizes floor(n/m) and floor(n/m)+1, and the block-count decomposition, as a finite statement on Fin n or Finset ranges.
2. The all-cut block bound (D) from the existing IntervalEnvelope and IntervalSuffix, with the block counts expressed through arbitrary functions, followed by the telescoping identity and the completing-square bound. Prefer a statement generic over an ordered ring if that kernel-checks, so that it can instantiate to the reals later; otherwise use integers or rationals with explicit denominators, and record exactly which form you used and why.
3. The deterministic finite-grid CDF envelope for monotone count functions, as a finite inequality with no measure and no real analysis.
Do NOT work on IntervalSampling, IntervalLiteral, product measures, integrals, the marginal CDFs, or the limit in this round; they are blocked at the kernel-check wall and root has asked the user about that wall. inputs/drafts-r1 holds them as inputs only. Do not retry them unchanged.

Your FIRST new-proof work is item 1, with an immediate strict compile and kernel check. A module that compiles but fails its kernel check is NOT certified. Use minimal imports and small modules. If an import graph fails the kernel check, try one genuinely smaller graph, then record the exact failure and move on; do not loop. No cap or limit increase is authorized. Every Lean process uses -j1, -M3500 or stricter, LEAN_NUM_THREADS 1 and the same AS 6GiB, RSS 6GiB and CPU 115 caps. No sorry, admit, added axiom, unsafe, native_decide or external solver; only propext, Classical.choice and Quot.sound. Preserve every failure with its true exit. Every new green module needs compile, checker, scoped axioms and a checkpoint with exact hashes. Keep results/336276.json strict_green_modules complete. When the finite items are done or genuinely blocked, re-run the source-only empty-build replay over all green modules with replay_driver.py, then seal.

Seal standalone frozen-after, then an exhaustive own-byte manifest, with exact terminal noncircular exclusions. Credit 0, 57 of 60 unchanged. Root alone adjudicates.

INHERITED FULL TASK (the override above controls all conflicts):
'''
(L/'TASK.txt').write_text(override+task)
save(L/'INPUT-ORIGINS.json',origins);save(L/'ROOT-PREP.json',dict(utc=now,lane=str(L),mathdb_id=336276,model='gpt-6.1-sol',reasoning='high',service='default',prospective_scientific_pass=True,credit=0,accepted_new=57,children=False,network=False,root_math_or_Lean_execution=False,protected_peers=peers))
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=336276,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),baseline_modules=len(baseline),model='gpt-6.1-sol',reasoning='high',service='default',credit=0,accepted_new=57,protected_peers=peers)
save(ROOT/'interval-kwidth-formal-r2-ready.json',ready);save(ROOT/'selection-routing-interval-kwidth-formal-r2.json',dict(ids=[336276],sources=['https://arxiv.org/abs/1706.01230'],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
print(json.dumps(dict(r1_manifest=325,frozen=35,green=len(green),evidence=dict(count=ev['count'],lanes=ev['lanes'],max_rss=ev['max_sampled_rss_bytes']),r2=ready,credit=0,accepted_new=57)))
