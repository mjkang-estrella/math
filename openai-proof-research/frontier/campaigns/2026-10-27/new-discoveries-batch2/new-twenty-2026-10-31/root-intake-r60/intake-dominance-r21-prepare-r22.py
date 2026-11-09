"""Root documentary verification of the 382297 state-dominance Lean lane r21 and preparation of its continuation r22. No root Lean or mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,shutil,re
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');assert led['accepted_new']==57 and led['target_new']==80
F=P/'transitive-bunkbed-state-dominance-formal-sol-r21';L=P/'transitive-bunkbed-state-dominance-formal-sol-r22';assert not L.exists()
pins=read(F/'PINS.json')
def jsonrows(q):
 out=[]
 for line in q.read_text(errors='replace').splitlines():
  try:v=json.loads(line)
  except ValueError:continue
  if isinstance(v,dict):out.append(v)
 return out

# Every documentary check precedes any root mutation.
fex=manifest(F,'MANIFEST.json',245,'seal_manifest','terminal_noncircular_self_exclusions');frozen(F,33)
assert sha(F/'TASK.txt')==read(ROOT/'bunkbed-dominance-r21-ready.json')['task_sha256']
expected={n+'.receipt.json':1 for n in ['abstract_v1','abstract_v2','abstract_v3','fiber_v1','fiber_v2','fiber_v4','tools_v1','pins_v1','recursion_v2','endpoint_source_v1','recursion_v3','increment_zero_v1','recursion_v4','recursion_v5','increment_zero_v2']}
frec=[];G6=6*1024**3;G32=32*1024**3
for q in sorted(F.glob('*.receipt.json')):
 v=read(q);lean='formal_command.py' in ' '.join(v['command'])
 assert v['cwd']==str(F) and v['cpu_limit_s']==115 and v['group_rss_guard_bytes']==G6 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None,q.name
 assert v['as_limit_bytes']==(G32 if lean else G6),q.name
 assert v['exit']==expected.get(q.name,0),(q.name,v['exit']);frec.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
result=read(F/'results/382297.json');green=result['strict_green_modules'];assert len(green)==20 and sum(1 for x in green if not x['baseline'])==6 and result['step_4_reached'] is False and result['final_theorem_proven'] is False
trio={'propext','Classical.choice','Quot.sound'};base=read(F/'BASELINE.json')
for row in green:
 m=row['name'];c=next(x for x in jsonrows(F/(row['compile_label']+'.output.txt')) if x.get('stage')=='compile' and x.get('module')==m);k=next(x for x in jsonrows(F/(row['check_label']+'.output.txt')) if x.get('stage')=='check' and x.get('module')==m)
 assert c['exit']==k['exit']==0 and read(F/(row['compile_label']+'.receipt.json'))['exit']==read(F/(row['check_label']+'.receipt.json'))['exit']==0,m
 s=sha(F/'src'/(m+'.lean'));o=sha(F/'build'/(m+'.olean'));assert s==row['source_sha256']==c['source_sha256_after']==k['source_sha256_after'] and o==row['olean_sha256']==c['olean_sha256_after']==k['olean_sha256_before']==k['olean_sha256_after'],m
 assert c['argv'][0]==pins['lean_bin'] and all(x in c['argv'] for x in ['-j1','-M3500','-DwarningAsError=true']) and k['argv']==[pins['leanchecker_bin'],m] and c['LEAN_NUM_THREADS']==k['LEAN_NUM_THREADS']==1,m
 found=re.findall(r'depends on axioms: \[([^\]]*)\]',(F/(row['audit_label']+'.output.txt')).read_text(errors='replace'));assert found,m
 assert all({y.strip() for y in f.split(',')}<=trio for f in found),m;assert read(F/(row['audit_label']+'.receipt.json'))['exit']==0
 assert not re.search(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|^\s*axiom\b',(F/'src'/(m+'.lean')).read_text(),re.M),m
for row in base['modules']:assert sha(F/'src'/(row['module']+'.lean'))==row['source_sha256']
for out in F.glob('*.output.txt'):
 pass
for f in ['src/BunDomIncrementCounts.lean','attempts/BunDomRecursion_v5.lean','SUMMARY.md']:assert (F/f).is_file(),f

fs='382297 uncredited formal r21 PARTIAL. Root verified 20 modules, compile and kernel check with source and olean hashes and scoped axioms: 14 baseline replayed from empty and 6 new. New: BunDomAbstract (abstract reflected-mass dominance and payoff), BunDomFiber (actual assignment split, fiber size 2^(2j+3)), BunDomPins, BunDomZero (generic pinned-bit counts), BunDomRecursion (res_join, hor_join, stf_join and generic transport), BunDomEndpoint (the source case j=u only). Unpaid: four increment-specific fiber counts, the count-only recursion, the initial half and half law, weight equivariance and no-crossing on actual fibers, and the general state-level inequality for u<j. A specialized transport repeatedly exhausted default heartbeats at whnf. Fifteen failed compile attempts retained with true exits. 245 manifest files, 33 frozen bindings. Credit 0, 57/80.'
fr=dict(utc=now,mathdb_id=382297,source_lane=str(F),manifest_sha256=sha(F/'MANIFEST.json'),verified_manifest_files=245,verified_frozen_bindings=33,green_modules=green,runner_receipts=frec,result=result,scientific_summary=fs,root_disposition='INCOMPLETE_UNCREDITED_FORMAL_RESEARCH_CONTINUE',credit=0,accepted_new=57,terminal_self_exclusions=sorted(fex),root_scope='Documentary integrity only; no Lean by root.')
save(P/'transitive-bunkbed-state-dominance-formal-parent-integration-r21.json',fr)

L.mkdir();origins={}
def copy(src,rel):
 d=L/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,d);assert sha(src)==sha(d);origins[rel]=dict(path=str(src),sha256=sha(src))
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','PINS.json','formal_command.py','run_lean_32g.py','check32.sh','checker32.sh','model-policy-sol-only.json']:copy(F/h,h)
for h in ['check32.sh','checker32.sh']:(L/h).chmod(0o755)
for d in ['src','build','cache','audit','results','logs']:(L/d).mkdir(exist_ok=True)
baseline=[]
for row in green:
 m=row['name'];copy(F/'src'/(m+'.lean'),'src/'+m+'.lean');blobs=[]
 for q in sorted((F/'build').glob(m+'.*')):
  if q.is_file():copy(q,'build/'+q.name);blobs.append(dict(path='build/'+q.name,sha256=sha(q)))
 baseline.append(dict(row,blobs=blobs))
for q in sorted((F/'inputs').rglob('*')):
 if q.is_file():copy(q,str(Path('inputs')/q.relative_to(F/'inputs')))
copy(F/'src/BunDomIncrementCounts.lean','inputs/drafts-r21/BunDomIncrementCounts.lean');copy(F/'attempts/BunDomRecursion_v5.lean','inputs/drafts-r21/BunDomRecursion_v5.lean');copy(F/'SUMMARY.md','inputs/r21-SUMMARY.md');copy(F/'results/382297.json','inputs/r21-results.json')
save(L/'BASELINE.json',dict(origin=str(F),root_verified_manifest_sha256=sha(F/'MANIFEST.json'),immutable_green_modules=baseline,rule='These twenty sources and all compiler sidecars are immutable. Import the sealed oleans from build/. Never run check32.sh on these names. New modules must use the prefix BunDom and new names.'))
save(L/'INPUT-ORIGINS.json',origins)
peers=['expanded-corpus-r528','transitive-bunkbed-reach-formal-deepseek-r20']
task=f'''MathDB 382297: state-level dominance in Lean, continuation r22. GPT-6.1 Sol high/default ONLY. Do the work yourself; no children or fallback model. Write ONLY inside {L}. Credit 0; campaign 57 of 80 unchanged.

GOAL. Prove, with the existing definitions unchanged and no added premise:
  theorem Bun.state_endpoint : ∀ (n u j : Nat), u ≤ j → j < n → Fintype.card {{w : Bun.Asg n j // j ∈ Bun.sval true (Bun.stf n u j w)}} ≤ Fintype.card {{w : Bun.Asg n j // j ∈ Bun.sval false (Bun.stf n u j w)}}

STATE OF PLAY. Root verified twenty modules, listed in BASELINE.json, with compile, kernel and axiom evidence. Read inputs/r21-SUMMARY.md and inputs/r21-results.json. Paid: BunDomAbstract (abstract reflected-mass dominance and payoff), BunDomFiber (assignment split, fiber size 2^(2j+3)), BunDomPins, BunDomZero, BunDomRecursion (res_join, hor_join, stf_join, generic transport), BunDomEndpoint (source case j=u only), and the fourteen baseline modules. The mathematics is in inputs/shortest-proof-PROOF.md. A separate protected lane handles the bridge to Reach; do NOT work on Reach.

FIRST command EXACTLY: timeout 20 python3 -I -B {L}/bootstrap.py
SECOND command EXACTLY: timeout 140 python3 -I -B {L}/verify_frozen.py before

RULES. Peers {peers[0]} and {peers[1]} and every other lane are protected: no read, stat, hash, list or glob. No network, git, installs, accounts, browser, other models, mathematical programs, solvers or background jobs. Do not modify helpers, PINS, inputs or the twenty baseline sources and sidecars, and never run check32.sh on their names. Authored files go through {L}/write_lane.py RELATIVE_PATH with content on stdin. Non-Lean local work goes through: timeout 140 python3 -I -B {L}/run.py UNIQUE_LABEL with Python on stdin.
Lean runs only through these wrappers, one at a time, each with a unique receipt label:
  {L}/check32.sh MODULE LABEL     compile src/MODULE.lean strictly
  {L}/checker32.sh MODULE LABEL   kernel-check the compiled module
They use a 32 GiB address-space limit, approved by the user for Lean only. Unchanged: 6 GiB real memory, CPU 115 s, -j1, -M3500, LEAN_NUM_THREADS 1, -DwarningAsError=true. Use specific mathlib imports. Do not raise any process limit. You MAY use `set_option maxHeartbeats N in` on a declaration where that genuinely helps and it still finishes within the CPU limit, and you may split modules freely. No unchanged retries; every changed attempt needs a new label. Keep every failure and its true exit. New module names use the prefix BunDom and must differ from the baseline names.

ROUTE, in order. Start writing real Lean at once.
1. FOUR INCREMENT COUNTS. For a fixed prefix p : Asg n j with old reachable sets of sizes a and b, count the extensions by (x,y,z). The cleanest statement avoids dependent types: over fresh data (Fin (j+1) → Bool → Bool) × Bool, x depends only on the layer-false row restricted to the old set, and y only on the layer-true row restricted to the other old set. These are independent coordinates, so the count is a product. Prove the product form generically, for arbitrary Finsets, using BunDomPins and BunDomZero, then transport once. inputs/drafts-r21/BunDomIncrementCounts.lean is a failed direct attempt.
2. COUNT RECURSION. Let N j (a,b) be the number of w : Asg n j with state cardinalities (a,b). r21's specialized transport exhausted heartbeats at whnf on stf; see inputs/drafts-r21/BunDomRecursion_v5.lean. Avoid unfolding: state the transport for an arbitrary function F : Asg n j → α and an arbitrary predicate, and instantiate only after making the state function opaque, for example with `generalize`, a local irreducible definition, or by working through Finset.card_eq_sum_card_fiberwise on the map to the state pair. Prove the weights satisfy the equivariance and no-crossing hypotheses of BunDomAbstract, and use Bun.stf_old_mem_iff, Bun.stf_upper_support and the new-index identities for the increment. Every old reachable index is a predecessor of the new one.
3. INITIAL LAW at j=u: half (1,0), half (1,1). BunDomEndpoint has the source facts.
4. PAYOFF AND ENDPOINT. Clear denominators in E(U-V | a,b) proportional to 2^-b - 2^-a, apply BunDomAbstract, and conclude Bun.state_endpoint.

SUSTAIN. Do not stop at a helper. If one route blocks, keep the source and exact diagnostic and try a genuinely different one before stopping. A module that compiles but fails its kernel check is NOT green. Never add sorry, admit, axiom, unsafe, native_decide, a weakened target or a conclusion-bearing premise.

EVIDENCE. Every new green module needs a passing compile, a passing kernel check, and an audit module with #print axioms for each main theorem, compiled through check32.sh. Only propext, Classical.choice and Quot.sound are allowed. Keep results/382297.json updated with strict_green_modules (name, source_sha256, olean_sha256, compile_label, check_label, audit_label, baseline), including the twenty baseline rows copied from BASELINE.json, plus exact_final_theorem_statement, final_theorem_proven and an unpaid list. Write SUMMARY.md at the end, honest about partial progress.

SEAL. Run timeout 140 python3 -I -B {L}/verify_frozen.py after, then under run.py with label seal_manifest write MANIFEST.json: a dict with count, credit 0, files as a list of objects with path, sha256 and bytes covering every lane file except the three terminal ones, and terminal_noncircular_self_exclusions listing exactly MANIFEST.json, seal_manifest.receipt.json and seal_manifest.output.txt. Stop at handback.
'''
(L/'TASK.txt').write_text(task)
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=382297,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),baseline_modules=len(baseline),model='gpt-6.1-sol',reasoning='high',service='default',credit=0,accepted_new=57,target_new=80,protected_peers=peers)
save(ROOT/'bunkbed-dominance-r22-ready.json',ready);save(ROOT/'selection-routing-bunkbed-dominance-r22.json',dict(ids=[382297],sources=['https://arxiv.org/abs/2406.01790'],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
print(json.dumps(dict(r21_manifest=245,frozen=33,green=len(green),failures=len(expected),next=ready,credit=0,accepted_new=57)))
