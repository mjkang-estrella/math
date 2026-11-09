"""Root preparation of the 382297 Lean continuation on Pi DeepSeek under the 32 GiB Lean runner; records the user's model permission. No root Lean or mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,shutil,re
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');assert led['accepted_new']==57 and led['target_new']==80
MODEL='spark/DeepSeek-V4.1-Flash-1017'
L=P/'transitive-bunkbed-reach-formal-deepseek-r20';assert not L.exists()
D=P/'lean-address-space-diagnostic-sol-r1';R=P/'transitive-bunkbed-new-indicators-formal-pi-r19'
assert read(ROOT/'lean-cap-policy-20261108.json')['runner_sha256']==sha(D/'run_lean_32g.py')
sources=sorted((R/'src').glob('*.lean'));assert len(sources)==14
deps={}
for q in sources:
 s=q.read_text();assert not re.search(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|^\s*axiom\b',s,re.M),q.name
 deps[q.stem]={m for m in re.findall(r'^import (\S+)',s,re.M) if m.startswith('Bun')}
assert all(v<=set(deps) for v in deps.values())
order=[];left=dict(deps)
while left:
 ready=sorted(m for m,v in left.items() if v<=set(order));assert ready;order+=ready
 for m in ready:del left[m]
inputs={'inputs/literal-target.json':P/'transitive-bunkbed-source-review-r1/literal-target.json','inputs/source-review-REVIEW.md':P/'transitive-bunkbed-source-review-r1/REVIEW.md','inputs/ordinary-proof-CANDIDATE.md':P/'expanded-corpus-r334/CANDIDATE.md','inputs/semantic-plan-REVIEW.md':P/'transitive-bunkbed-semantic-plan-review-r3/REVIEW.md','inputs/semantic-plan-NEXT-BRIEF.md':P/'transitive-bunkbed-semantic-plan-review-r3/NEXT-PI-BRIEF.md','inputs/semantic-adjudication-r3.json':P/'transitive-bunkbed-semantic-review-parent-adjudication-r3.json','inputs/parent-qualification-r1.json':P/'transitive-bunkbed-parent-qualification-r1.json','inputs/r19-SUMMARY.md':R/'SUMMARY.md','inputs/r19-integration.json':P/'transitive-bunkbed-formal-parent-integration-r19.json'}
for v in inputs.values():assert v.is_file(),v

L.mkdir();origins={}
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','PINS.json','formal_command.py','run_lean_32g.py','check32.sh','checker32.sh']:
 shutil.copyfile(D/h,L/h);assert sha(D/h)==sha(L/h);origins[h]=dict(path=str(D/h),sha256=sha(D/h))
for h in ['check32.sh','checker32.sh']:(L/h).chmod(0o755)
for d in ['src','build','cache','audit','results','logs']:(L/d).mkdir()
base=[]
for q in sources:
 d=L/'src'/q.name;shutil.copyfile(q,d);assert sha(q)==sha(d);origins['src/'+q.name]=dict(path=str(q),sha256=sha(q));base.append(dict(module=q.stem,source_sha256=sha(q)))
for rel,q in inputs.items():
 d=L/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,d);assert sha(q)==sha(d);origins[rel]=dict(path=str(q),sha256=sha(q))
policy=dict(utc=now,user_instruction='You can use pi/deepseek for a subagent',provider='pi',model=MODEL,options=dict(thinking='high'),scope='Additional permitted model. GPT-6.1 Sol remains the default for discovery and scientific qualification. Three-delegate cap unchanged.')
save(ROOT/'model-policy-pi-deepseek-20261108.json',policy);save(L/'model-policy.json',policy)
save(L/'BASELINE.json',dict(origin=str(R),build_order=order,modules=base,rule='Baseline sources are immutable. Rebuild them from empty in build_order. Add new modules; do not edit these.'))
save(L/'INPUT-ORIGINS.json',origins)
peers=['expanded-corpus-r525','expanded-corpus-r526']
task=f'''MathDB 382297: Lean continuation toward the literal endpoint. Pi DeepSeek V4.1 Flash, high thinking. Do the work yourself; no children. Write ONLY inside {L}. Credit 0; campaign 57 of 80 unchanged.

TARGET. The bunkbed conjecture in the E7/D7 model for transitive tournaments (Hollom, arXiv:2406.01790). The literal endpoint, using the existing definitions in src/BunkbedBase.lean unchanged:
  for all n and all u v : Fin n, the number of outcomes omega : Out n with Reach n omega (u,false) (v,true) is at most the number with Reach n omega (u,false) (v,false).
A complete ordinary proof exists and passed independent review. It is in inputs/ordinary-proof-CANDIDATE.md, with the semantic route in inputs/semantic-plan-REVIEW.md and inputs/semantic-plan-NEXT-BRIEF.md. Fourteen baseline modules in src/ already prove the state machinery. Read inputs/r19-SUMMARY.md and inputs/r19-integration.json for exactly what is paid.

FIRST command EXACTLY: timeout 20 python3 -I -B {L}/bootstrap.py
SECOND command EXACTLY: timeout 140 python3 -I -B {L}/verify_frozen.py before

RULES. Peers {peers[0]} and {peers[1]} and every other lane are protected: no read, stat, hash, list or glob. No network, git, installs, accounts, browser, other models, mathematical programs, solvers or background jobs. Do not modify helpers, PINS, inputs or baseline sources. Authored files go through {L}/write_lane.py RELATIVE_PATH with content on stdin. Non-Lean local work goes through: timeout 140 python3 -I -B {L}/run.py UNIQUE_LABEL with Python on stdin.
Lean runs only through these two wrappers, one at a time, each with a unique receipt label:
  {L}/check32.sh MODULE LABEL     compile src/MODULE.lean strictly
  {L}/checker32.sh MODULE LABEL   kernel-check the compiled module
They apply a 32 GiB address-space limit, approved by the user for Lean only and confirmed by a diagnostic. Unchanged: 6 GiB real memory, CPU 115 s, -j1, -M3500, LEAN_NUM_THREADS 1, -DwarningAsError=true. Use specific mathlib imports. `import Mathlib` is killed by the real-memory guard. Do not raise any limit. Keep modules small. If one is slow, split it. No unchanged retries; every changed attempt needs a new label. Keep every failure and its true exit.

STEP 0: BASELINE REPLAY. Compile and then kernel-check all fourteen modules, in BASELINE.json build_order, from the empty build directory. Labels base_compile_MODULE and base_check_MODULE. If a baseline module fails, record it exactly, do not edit it, and report it at handback. Continue only if its dependents can still be built.

STEP 1: LITERAL REACH BRIDGE. Prove, for u i : Fin n, j : Nat with j < n, sigma : Bool and omega : Out n, the membership equivalence in inputs/semantic-plan-NEXT-BRIEF.md:
  i.val is in sval sigma (stf n u.val j (wres n j omega)) if and only if i.val <= j and Reach n omega (u,false) (i,sigma).
Include the endpoint specialization i = j and the v < u and v = u cases. Use the joint prefix induction the brief describes: state to Reach through the closed X or (Z and Y) form; Reach to state by an inner derivation induction with the generalized low-endpoint bound. Do not try to solve the cyclic reach_char equations by rewriting; X=Y=0, Z=1 has a spurious fixed point. As soon as you have read the brief, write a real attempt to a new module and compile it, before any wider exploration.

STEP 2: COUNTING. In new modules, build the fresh-token split, the integer fiber counts 2^(2m-a-b) times (2, 2^a-1, 2^b-1, 2^(a+b+1)-2^a-2^b), the initial biased law, the reflection DOMINANCE induction, the terminal payoff and the outside-window factors, over Nat and Int with no probability or measure theory. The brief explicitly rejects r2's stf/flipAsg swap and same-source reflected fiber equality; n=1, u=j=0, z=0 refutes them. Source event counts at v=u are 2^(n^2) and 2^(n^2-1).

STEP 3: ENDPOINT. State and prove the literal theorem above as Bun.bunkbed_E7_transitive with no extra hypotheses, covering v < u, v = u and u < v, and with no count-kernel or fiber statement as a premise.

SUSTAIN. Do not stop at one helper. Work through the steps as far as you can. If you are blocked, keep the source and the exact diagnostic, try a genuinely different route, and only then stop with a precise statement of what is unpaid. A module that compiles but fails its kernel check is NOT green. Never add sorry, admit, axiom, unsafe or native_decide, a conclusion-bearing premise, a weakened target or a proxy definition.

EVIDENCE. Every green module needs a passing compile and a passing kernel check, and an audit: a small module AuditNAME.lean importing it with #print axioms for each new main theorem, compiled through check32.sh. Only propext, Classical.choice and Quot.sound are allowed. Keep results/382297.json updated with strict_green_modules (name, source sha256, olean sha256, compile label, check label, audit label), the steps completed, and an unpaid list. Write SUMMARY.md at the end, honest about partial progress.

SCIENTIFIC STATUS. Ordinary proof independently passed; prior-art qualification is bounded, the Przybylowski final journal version is unread and closed, and a second adversarial qualification is still to come. Acceptance is root-only and may be refused. Do not claim credit.

SEAL. Run timeout 140 python3 -I -B {L}/verify_frozen.py after, then under run.py with label seal_manifest write MANIFEST.json: a dict with count, credit 0, files as a list of objects with path, sha256 and bytes covering every lane file except the three terminal ones, and terminal_noncircular_self_exclusions listing exactly MANIFEST.json, seal_manifest.receipt.json and seal_manifest.output.txt. Stop at handback.
'''
(L/'TASK.txt').write_text(task)
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=382297,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),baseline_modules=len(base),build_order=order,provider='pi',model=MODEL,thinking='high',credit=0,accepted_new=57,target_new=80,protected_peers=peers)
save(ROOT/'bunkbed-deepseek-r20-ready.json',ready);save(ROOT/'selection-routing-bunkbed-deepseek-r20.json',dict(ids=[382297],sources=['https://arxiv.org/abs/2406.01790'],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
led['model_allocation_update']['additional_permitted_20261108']=policy
led['process_notes'].append(dict(utc=now,item='Pi DeepSeek V4.1 Flash permitted for a subagent by the user; 382297 Lean continuation prepared in transitive-bunkbed-reach-formal-deepseek-r20.'))
(P/'ledger.json').write_text(json.dumps(led,indent=2)+'\n')
with (P/'AGENTS.md').open('a') as q:q.write("\nModel note 2026-11-08: the user also permits Pi `spark/DeepSeek-V4.1-Flash-1017` for a subagent; GPT-6.1 Sol stays the default for discovery and scientific qualification.\n")
print(json.dumps(dict(ready=ready)))
