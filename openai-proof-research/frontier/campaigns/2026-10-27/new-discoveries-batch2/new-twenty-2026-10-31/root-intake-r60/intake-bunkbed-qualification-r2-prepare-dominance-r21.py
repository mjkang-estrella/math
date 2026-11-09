"""Root documentary verification and scientific disposition of the 382297 second qualification, and preparation of a parallel Lean lane for the state-level dominance inequality. Root hand-checked the short displayed proof only; no root Lean."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,shutil,re,collections
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');assert led['accepted_new']==57 and led['target_new']==80
Q=P/'transitive-bunkbed-primary-qualification-sol-r2';B=P/'transitive-bunkbed-reach-formal-deepseek-r20';L=P/'transitive-bunkbed-state-dominance-formal-sol-r21';assert not L.exists()

# Every documentary check precedes any root mutation.
m=read(Q/'SHA256-MANIFEST.json');assert len(m['files'])==193==m['count']
names=set()
for x in m['files']:
 n=x['path'];assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=Q/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
qex=sorted(m['terminal_exclusions']);assert set(qex)=={'SHA256-MANIFEST.json','terminal_seal.receipt.json','terminal_seal.output.txt'}
inventory=set()
for q in Q.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(Q)))
assert inventory==names|set(qex)
frozen(Q,46);qrec=receipts(Q,{'scopes3_cactus_link.receipt.json':1})
assert sha(Q/'TASK.txt')==read(ROOT/'bunkbed-qualification-r2-ready.json')['task_sha256']
qbudget=search(Q,2,6,2,6,['search/full-one.json','search/full-two.json'])
qe=guard(Q,[Q/f'plans/get-{x}.json' for x in ['cactus-abs','cactus-pdf','forest-abs','forest-pdf','reflection']],[382297],dict(attempt=5,success=5),2)
review=read(Q/'review.json');assert set(review)=={'382297'};g=review['382297'];assert g['recommendation']=='CREDITABLE SUBJECT TO LEAN AND PAPER'
for f in ['PROOF.md','REVIEW.md','source-map.json','family-comparison.json']:assert (Q/f).is_file()
assert sha(B/'src/BunNewIndicators.lean')==read(B/'frozen-inputs.json')[str(B/'src/BunNewIndicators.lean')]

qs='382297 second adversarial qualification: ordinary proof and exact model PASS, literal PASS, recommendation CREDITABLE SUBJECT TO LEAN AND PAPER. Root adopts a PROSPECTIVE SCIENTIFIC PASS with modest significance and bounded novelty; credit 0 until the literal Lean endpoint, independent formal audit, paper and fresh extracted replay are all paid, and root may still refuse. Root hand-checked the displayed short proof: the four increment probabilities qr, (1-q)r/2, q(1-r)/2, 1-(q+r)/2 from U=X or ZY, V=Y or ZX; reflection equivariance; no crossing of the diagonal because a-b changes by at most one; the paired-sum induction using K(s,rho t)=K(rho s,t) with the cross term zero; initial law half (1,0), half (1,1); and payoff (2^-b-2^-a)/2. Basis: the reviewer tried and failed to obtain a direct injection, an old complete-graph transfer (van Hintum-Lammers, Leander) or a Przybylowski bridge; Hollom\'s journal paper calls tournaments approachable but unexpectedly difficult and says complete-graph methods lack the needed symmetries, and the thesis restates the conjecture after the acyclic counterexample. The routine-exclusion rule needs a complete applicable prior bridge and none was found. Strongest objection retained: about a 300-word proof by an old skip-free reflection idea, with E7 a parameter instance of a reviewer-derived column-homogeneous law; no credit attaches to that extension. Limits retained: the acyclic final, DOI 10.1016/j.ejc.2025.104289, is closed and unread; registry roots closed; bounded search, not worldwide novelty. Process: raw JSONL read after the author proposal, disclosed. 193 manifest files, 46 frozen bindings verified.'
qr=dict(utc=now,mathdb_id=382297,source_lane=str(Q),manifest_sha256=sha(Q/'SHA256-MANIFEST.json'),verified_manifest_files=193,verified_frozen_bindings=46,review=g,source_map=read(Q/'source-map.json'),runner_receipts=qrec,guard_events=dict(collections.Counter(e['event'] for e in qe)),search_budget=qbudget,scientific_summary=qs,reviewer_recommendation='CREDITABLE SUBJECT TO LEAN AND PAPER',root_disposition='PROSPECTIVE_SCIENTIFIC_PASS_MODEST_SIGNIFICANCE_BOUNDED_NOVELTY_LEAN_CONTINUES',credit=0,accepted_new=57,terminal_self_exclusions=qex,root_scope='Documentary integrity, root hand-check of the displayed short proof and scientific disposition; no Lean by root.')
save(P/'transitive-bunkbed-qualification-parent-integration-r2.json',qr)
den=read(ROOT/'inherited-denials-r559.json');den['utc']=now;den['root_bunkbed382297_qualification_r2_scope']=qs;denpath=ROOT/'inherited-denials-r560.json';save(denpath,den)
for c in led['candidates']:
 if int(c['mathdb_id'])==382297:c['status']='second adversarial qualification PASS; root prospective scientific pass, modest significance, bounded novelty; Lean endpoint in progress; credit 0';c['second_qualification']='transitive-bunkbed-qualification-parent-integration-r2.json'
led['process_notes'].append(dict(utc=now,item='382297 prospective scientific pass recorded; parallel state-dominance Lean lane prepared.'))
(P/'ledger.json').write_text(json.dumps(led,indent=2)+'\n')

L.mkdir();origins={}
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','PINS.json','formal_command.py','run_lean_32g.py','check32.sh','checker32.sh']:
 shutil.copyfile(B/h,L/h);origins[h]=dict(path=str(B/h),sha256=sha(B/h))
for h in ['check32.sh','checker32.sh']:(L/h).chmod(0o755)
shutil.copyfile(Q/'model-policy-sol-only.json',L/'model-policy-sol-only.json')
for d in ['src','build','cache','audit','results','logs']:(L/d).mkdir()
base=read(B/'BASELINE.json')
for row in base['modules']:
 q=B/'src'/(row['module']+'.lean');assert sha(q)==row['source_sha256'];shutil.copyfile(q,L/'src'/q.name);origins['src/'+q.name]=dict(path=str(q),sha256=sha(q))
inputs={'inputs/shortest-proof-PROOF.md':Q/'PROOF.md','inputs/second-review-REVIEW.md':Q/'REVIEW.md','inputs/ordinary-proof-CANDIDATE.md':B/'inputs/ordinary-proof-CANDIDATE.md','inputs/literal-target.json':B/'inputs/literal-target.json','inputs/semantic-plan-REVIEW.md':B/'inputs/semantic-plan-REVIEW.md','inputs/r19-SUMMARY.md':B/'inputs/r19-SUMMARY.md'}
for rel,q in inputs.items():
 d=L/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,d);origins[rel]=dict(path=str(q),sha256=sha(q))
save(L/'BASELINE.json',dict(base,origin=str(B),rule='Baseline sources are immutable. Rebuild them from empty in build_order. New modules must be named with the prefix BunDom.'))
save(L/'INPUT-ORIGINS.json',origins)
peers=['expanded-corpus-r527','transitive-bunkbed-reach-formal-deepseek-r20']
task=f'''MathDB 382297: state-level dominance in Lean. GPT-6.1 Sol high/default ONLY. Do the work yourself; no children or fallback model. Write ONLY inside {L}. Credit 0; campaign 57 of 80 unchanged.

CONTEXT. The bunkbed conjecture in the E7/D7 model for transitive tournaments now has a prospective scientific pass, with Lean still required. The short proof is in inputs/shortest-proof-PROOF.md and the fuller one in inputs/ordinary-proof-CANDIDATE.md. Fourteen baseline modules in src/ define the prefix state machine; read inputs/r19-SUMMARY.md for what is paid, including Bun.stf_old_mem_iff, Bun.stf_upper_support, and the new-index identities Bun.stf_new_mem_fst_iff and Bun.stf_new_mem_snd_iff.

DIVISION OF LABOUR. A separate protected lane is proving the literal bridge between Reach and the state machine. Do NOT work on Reach. Your job is everything on the state-machine side, ending in the inequality in Step 4. The later assembly combines the two.

FIRST command EXACTLY: timeout 20 python3 -I -B {L}/bootstrap.py
SECOND command EXACTLY: timeout 140 python3 -I -B {L}/verify_frozen.py before

RULES. Peers {peers[0]} and {peers[1]} and every other lane are protected: no read, stat, hash, list or glob. No network, git, installs, accounts, browser, other models, mathematical programs, solvers or background jobs. Do not modify helpers, PINS, inputs or baseline sources. Authored files go through {L}/write_lane.py RELATIVE_PATH with content on stdin. Non-Lean local work goes through: timeout 140 python3 -I -B {L}/run.py UNIQUE_LABEL with Python on stdin.
Lean runs only through these wrappers, one at a time, each with a unique receipt label:
  {L}/check32.sh MODULE LABEL     compile src/MODULE.lean strictly
  {L}/checker32.sh MODULE LABEL   kernel-check the compiled module
They apply a 32 GiB address-space limit, approved by the user for Lean only. Unchanged: 6 GiB real memory, CPU 115 s, -j1, -M3500, LEAN_NUM_THREADS 1, -DwarningAsError=true. Use specific mathlib imports; `import Mathlib` is killed by the real-memory guard. Do not raise any limit. Keep modules small. No unchanged retries; every changed attempt needs a new label. Keep every failure and its true exit. Name every new module with the prefix BunDom.

STEP 0: BASELINE REPLAY. Compile and then kernel-check the fourteen modules in BASELINE.json build_order from the empty build directory. Labels base_compile_MODULE and base_check_MODULE. If one fails, record it exactly and do not edit it.

STEP 1: ABSTRACT REFLECTION THEOREM, module BunDomAbstract, with no dependence on the bunkbed definitions. Over Nat states (a,b) and integer or natural weights: let F_t be defined by a one-step recursion F_(t+1)(s') = sum over s of F_t(s) w_t(s,s') with finite support. Assume w_t(a,b,a',b') = w_t(b,a,b',a') and w_t(a,b,a',b') = 0 when a>b and a'<b'. If F_0(a,b) >= F_0(b,a) for a>b, then F_t(a,b) >= F_t(b,a) for a>b and all t. Also prove the payoff consequence: for g antisymmetric and nonnegative above the diagonal, the sum of F_t(s) g(s) is nonnegative. This is the paired-sum identity in the short proof. Write and compile a real attempt to this module straight after Step 0, before wider exploration.

STEP 2: FRESH-TOKEN SPLIT, module BunDomFiber. Using the actual Asg, res, hor, fresV definitions unchanged, show that an assignment on window j+1 corresponds to its restriction to window j together with the fresh horizontal bits into column j+1 in each layer and the vertical bit. For a fixed prefix with old reachable counts a and b, count the extensions by the values of x, y, z. There are 2j+2 horizontal fresh bits (j+1 predecessors in each layer, indices 0 to j), so the fiber counts for increments (0,0), (1,0), (0,1), (1,1) are 2^(2j+2-a-b) times 2, 2^a-1, 2^b-1 and 2^(a+b+1)-2^a-2^b. Check this exponent against the actual definitions and use what the definitions give. Only tokens from reachable old copies matter.

STEP 3: COUNT RECURSION, module BunDomRecursion. Let N_j(a,b) be the number of w : Asg n j whose state pair (stf n u j w) has cardinalities (a,b). Using Bun.stf_old_mem_iff, Bun.stf_upper_support and the new-index identities, prove N_(j+1) is given by N_j and the fiber counts, with no conditioning beyond counts. Note that every old reachable index is a predecessor of the new one, because the tournament is transitive. Prove the weights are equivariant and cannot cross the diagonal, and handle the initial column at j=u, where the law is half (1,0) and half (1,1) in counts.

STEP 4: STATE-LEVEL INEQUALITY, module BunDomEndpoint. For all n, u, j with u <= j < n, prove
  card of w : Asg n j with j in sval true (stf n u j w)  <=  card of w : Asg n j with j in sval false (stf n u j w).
Read the exact forms of Asg, stf and sval from src/ and state it with those definitions. Use the payoff identity E(U-V | a,b) proportional to 2^-b - 2^-a, cleared to integers, and treat j=u separately. No Reach, no probability or measure theory, and no conclusion-bearing premise.

SUSTAIN. Do not stop at one helper. If blocked, keep the source and exact diagnostic, try a genuinely different route, and only then stop with a precise statement of what is unpaid. A module that compiles but fails its kernel check is NOT green. Never add sorry, admit, axiom, unsafe or native_decide.

EVIDENCE. Every green module needs a passing compile, a passing kernel check, and an audit module AuditNAME.lean with #print axioms for each main theorem, compiled through check32.sh. Only propext, Classical.choice and Quot.sound are allowed. Keep results/382297.json updated with strict_green_modules (name, source sha256, olean sha256, compile label, check label, audit label), steps completed, the exact final theorem statement, and an unpaid list. Write SUMMARY.md at the end, honest about partial progress.

SEAL. Run timeout 140 python3 -I -B {L}/verify_frozen.py after, then under run.py with label seal_manifest write MANIFEST.json: a dict with count, credit 0, files as a list of objects with path, sha256 and bytes covering every lane file except the three terminal ones, and terminal_noncircular_self_exclusions listing exactly MANIFEST.json, seal_manifest.receipt.json and seal_manifest.output.txt. Stop at handback.
'''
(L/'TASK.txt').write_text(task)
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=382297,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),baseline_modules=len(base['modules']),model='gpt-6.1-sol',reasoning='high',service='default',credit=0,accepted_new=57,target_new=80,protected_peers=peers)
save(ROOT/'bunkbed-dominance-r21-ready.json',ready);save(ROOT/'selection-routing-bunkbed-dominance-r21.json',dict(ids=[382297],sources=['https://arxiv.org/abs/2406.01790'],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
print(json.dumps(dict(qualification_manifest=193,frozen=46,disposition=qr['root_disposition'],next=ready,credit=0,accepted_new=57)))
