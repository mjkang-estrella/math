"""Root documentary verification and disposition of the 347063 qualification, and preparation of its first Lean lane on DeepSeek. No root Lean or mathematics."""
import os,resource,subprocess
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,collections,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');assert led['accepted_new']==58 and led['target_new']==80
Q=P/'zeckendorf-games-primary-qualification-claude-r1';T=P/'transitive-bunkbed-endpoint-assembly-formal-deepseek-r23';L=P/'zeckendorf-games-formal-deepseek-r1';assert not L.exists()

# Every documentary check precedes any root mutation.
m=read(Q/'MANIFEST.json');assert m['file_count']==166==len(m['files']) and m['credit']==0
names=set()
for x in m['files']:
 n=x['path'];assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=Q/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
qex=sorted(m['terminal_noncircular_self_exclusions']);assert set(qex)=={'MANIFEST.json','seal.output.txt','seal.receipt.json'}
inventory=set()
for q in Q.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(Q)))
assert inventory==names|set(qex)
frozen(Q,21);qrec=receipts(Q,{'scopes_accepted_c2.receipt.json':1})
assert sha(Q/'TASK.txt')==read(ROOT/'zeckendorf-qualification-r1-ready.json')['task_sha256']
charges=[json.loads(s) for s in (Q/'search-charges.jsonl').read_text().splitlines()];qbudget=read(Q/'search-budget.json');assert len(charges)==2 and qbudget==dict(calls_used=2,queries_used=2,maximum_calls=2,maximum_queries=6,charged_before_call=True) and all(sha(Q/c['plan'])==c['plan_sha256'] for c in charges)
qe=guard(Q,sorted(Q.glob('plans/get-*.json')),[347063],dict(attempt=6,success=6),6)
review=read(Q/'review.json');assert set(review)=={'347063'};g=review['347063'];assert g['recommendation']=='CREDITABLE SUBJECT TO LEAN AND PAPER' and str(g['credit'])=='0'
for f in ['PROOF.md','PROOF-ERRATUM.md','REVIEW.md','source-map.json','family-comparison.md']:assert (Q/f).is_file()
for f in ['inputs/author-candidate-347063.md','inputs/author-formal-plan-347063.md','inputs/literal347063.json']:assert (Q/f).is_file()
pdfs=sorted((Q/'sources').glob('*.pdf'));assert len(pdfs)>=1

qs='347063 independent adversarial qualification, Claude Opus 5.5: CREDITABLE SUBJECT TO LEAN AND PAPER for Combine Smallest only, moderate confidence. Literal: FAIL as written, PASS source-bound; the MathDB record says the game starts from the Zeckendorf decomposition, which gives zero moves, while source Definition 1.1 starts from n copies of F_1. Root rules that the record is a transcription defect, that its only coherent reading is the source game, and binds the endpoint to the exact source scope openly, following the accepted_exact_source_scope precedent; correcting the record earns nothing, and the user may rule otherwise. Part (a) SS(n)=phi^2 n + O(log^2 n): mathematics PASS but PUBLIC through Cusenza et al., Fibonacci Quarterly 60(1) (2022), identity (3.16), attributed and uncredited. Part (b) CS(n)=c n + O(sqrt(n) log n), c = 5/2 - phi + sum_{j>=2} 1/F_{2j} = 1.2064812: mathematics PASS with an independent reconstruction; no prior found in a bounded search; no linear potential can count these splits; no reduction to a source theorem found. ROOT RECORDS A PROSPECTIVE SCIENTIFIC PASS for the conjecture as completed by part (b), modest significance, bounded novelty, credit 0 until a literal Lean endpoint, independent formal audit, paper and replay are paid. Strongest objection retained: an elementary count of one deterministic algorithm with half of the conjecture already public. The reviewer found and corrected an endgame error in its own table in PROOF-ERRATUM.md; the author list was right. Limits: no MathSciNet, zbMATH or citation-index coverage. 166 manifest files, 21 frozen bindings, 6 GET successes (all PDF), 2 searches.'
qr=dict(utc=now,mathdb_id=347063,source_lane=str(Q),manifest_sha256=sha(Q/'MANIFEST.json'),verified_manifest_files=166,verified_frozen_bindings=21,review=g,source_map=read(Q/'source-map.json'),runner_receipts=qrec,guard_events=dict(collections.Counter(e['event'] for e in qe)),search_budget=qbudget,scientific_summary=qs,reviewer_recommendation='CREDITABLE SUBJECT TO LEAN AND PAPER (Combine Smallest only)',root_disposition='PROSPECTIVE_SCIENTIFIC_PASS_EXACT_SOURCE_SCOPE_PART_A_PUBLIC_MODEST_SIGNIFICANCE_LEAN_NEXT',credit=0,accepted_new=58,terminal_self_exclusions=qex,root_scope='Documentary integrity and scientific disposition only; no mathematics by root.')
save(P/'zeckendorf-games-qualification-parent-integration-r1.json',qr)
den=read(ROOT/'inherited-denials-r569.json');den['utc']=now;den['root_zeckendorf347063_qualification_r1_scope']=qs;denpath=ROOT/'inherited-denials-r570.json';save(denpath,den)
led['process_notes'].append(dict(utc=now,item='347063 prospective scientific pass under exact source scope; Lean started on DeepSeek. 352303 queued for qualification.'));(P/'ledger.json').write_text(json.dumps(led,indent=2)+'\n')

L.mkdir();origins={}
def copy(src,rel):
 d=L/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,d);assert sha(src)==sha(d);origins[rel]=dict(path=str(src),sha256=sha(src))
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','PINS.json','formal_command.py','run_lean_32g.py','check32.sh','checker32.sh']:copy(T/h,h)
for h in ['check32.sh','checker32.sh']:(L/h).chmod(0o755)
save(L/'model-policy.json',read(ROOT/'model-policy-claude-deepseek-20261109.json'))
for d in ['src','build','cache','audit','results','logs']:(L/d).mkdir()
for rel,q in {'inputs/reviewer-PROOF.md':Q/'PROOF.md','inputs/reviewer-PROOF-ERRATUM.md':Q/'PROOF-ERRATUM.md','inputs/reviewer-REVIEW.md':Q/'REVIEW.md','inputs/author-candidate-347063.md':Q/'inputs/author-candidate-347063.md','inputs/author-formal-plan-347063.md':Q/'inputs/author-formal-plan-347063.md','inputs/literal347063.json':Q/'inputs/literal347063.json'}.items():copy(q,rel)
(L/'inputs/sources').mkdir()
for q in pdfs:
 copy(q,'inputs/sources/'+q.name);r=subprocess.run(['pdftotext','-layout',str(q),str(L/'inputs/sources'/(q.stem+'.txt'))],capture_output=True);assert r.returncode==0,r.stderr
save(L/'INPUT-ORIGINS.json',origins)
peers=['expanded-corpus-r534','expanded-corpus-r535']
task=f'''MathDB 347063: Lean formalization of the Zeckendorf game move counts, first lane. Pi DeepSeek V4.1 Flash, high thinking. Do the work yourself; no children or fallback model. Write ONLY inside {L}. Credit 0; campaign 58 of 80 unchanged.

MATHEMATICS. Source: Li, Li, Miller, Mizgerd, Sun, Xia, Zhou, Deterministic Zeckendorf Games (inputs/sources). Indices F_1=1, F_2=2, F_(i+1)=F_i+F_(i-1). Start at n copies of F_1. Moves: A1: F_1,F_1 -> F_2. Cons(i), i>=2: F_(i-1),F_i -> F_(i+1). Split(2): F_2,F_2 -> F_1,F_3. Split(i), i>=3: F_i,F_i -> F_(i-2),F_(i+1). The game ends when no move is legal. Split Smallest plays splits smallest first, then A1, then Cons smallest first. Combine Smallest plays A1, then Cons smallest first, then splits smallest first. Check all of this against source Definition 1.1 and section 1.2 and report any difference.

TARGET THEOREMS, with phi=(1+sqrt 5)/2, F_0:=1 as the proofs use it, SS n and CS n the actual numbers of moves of the two deterministic games from n copies of F_1:
  (a) exists C, for all n>=2, |(SS n : Real) - phi^2 * n| <= C * (log n)^2
  (b) exists C, for all n>=2, |(CS n : Real) - c * n| <= C * sqrt n * log n, where c = 5/2 - phi + the sum over j>=2 of 1/F_(2j), as a tsum, with a proved bracket 1.206 < c < 1.207.
The proofs are in inputs/reviewer-PROOF.md, inputs/reviewer-PROOF-ERRATUM.md and inputs/author-candidate-347063.md. Read inputs/reviewer-REVIEW.md section 7 for cautions. The erratum matters: the endgame must be split by K and by Case 1, 2 and 3.

FIRST command EXACTLY: timeout 20 python3 -I -B {L}/bootstrap.py
SECOND command EXACTLY: timeout 140 python3 -I -B {L}/verify_frozen.py before

RULES. Peers {peers[0]} and {peers[1]} and every other lane are protected: no read, stat, hash, list or glob. No network, git, installs, accounts, browser, other models, mathematical programs, solvers or background jobs. Do not modify helpers, PINS or inputs. Authored files go through {L}/write_lane.py RELATIVE_PATH with content on stdin. Non-Lean local work goes through: timeout 140 python3 -I -B {L}/run.py UNIQUE_LABEL with Python on stdin.
Lean runs only through these wrappers, one at a time, with unique labels:
  {L}/check32.sh MODULE LABEL     compile src/MODULE.lean strictly
  {L}/checker32.sh MODULE LABEL   kernel-check the compiled module
Unchanged: 6 GiB real memory, CPU 115 s, -j1, -M3500, LEAN_NUM_THREADS 1, -DwarningAsError=true. Use specific mathlib imports; `import Mathlib` is killed by the memory guard. `set_option maxHeartbeats N in` is allowed where it helps within the CPU limit. Keep modules small. No unchanged retries; every changed attempt needs a new label. Keep every failure and its true exit. Name new modules with the prefix Zeck.

ROUTE. Start writing real Lean at once.
1. ZeckBase: positions as finitely supported functions from indices to counts, the literal move relation, the Fibonacci numbers with this indexing, value invariance, and terminal positions.
2. ZeckStrategy: Split Smallest and Combine Smallest as actual deterministic step functions, exactly matching the source priorities. Prove every game terminates, and define SS and CS as the actual number of steps from n copies of F_1. No fuel-bounded definition that could change the count. Use the reviewer's tail bound or a real potential; note the review's warning that the integer weight i+3 does not work.
3. Controls: small exact values of SS and CS by proof or by decide, checked by hand against the source tables or examples if it gives any, and a lemma that a game started from the Zeckendorf decomposition has zero moves, documenting the MathDB record's misstatement.
4. Part (a) by the exact potential w_j = j + 2 + psi (-psi)^j with psi = 1/phi. Part (a) is public, but the literal conjecture has two halves, so it is required.
5. Part (b): the exact state summary while a pool sits at even index p, with the lower state one integer L in [0,F_(p-1)) and each macro the rotation L -> L + F_(p-2) mod F_(p-1); the chip balance giving F_p - 1 splits per cycle; the assembly across levels with its error; the endgame by cases; and the constant.
6. ZeckEndpoint: Zeck.split_smallest_asymptotic and Zeck.combine_smallest_asymptotic as stated above, with no added premise.

SUSTAIN. Do not stop at a helper. Work as far as you can, in order. If blocked, keep the source and exact diagnostic, try a genuinely different route, and only then stop with a precise statement of what is unpaid. A later lane will continue, so leave a clean state. A module that compiles but fails its kernel check is NOT green. Never add sorry, admit, axiom, unsafe, native_decide, a weakened target, a conclusion-bearing premise, or a definition that changes the game.

EVIDENCE. Every green module needs a passing compile, a passing kernel check, and an audit module with #print axioms for each main theorem, compiled through check32.sh. Only propext, Classical.choice and Quot.sound are allowed. Keep results/347063.json updated with strict_green_modules (name, source_sha256, olean_sha256, compile_label, check_label, audit_label), steps completed, exact theorem statements, and an unpaid list. Write SUMMARY.md at the end, honest about partial progress.

STATUS. Prospective scientific pass, with modest significance; the Split Smallest half is already public and attributed. Acceptance is root-only and may be refused. Do not claim credit.

SEAL. Run timeout 140 python3 -I -B {L}/verify_frozen.py after, then under run.py with label seal_manifest write MANIFEST.json: a dict with count, credit 0, files as a list of objects with path, sha256 and bytes covering every lane file except the three terminal ones, and terminal_noncircular_self_exclusions listing exactly MANIFEST.json, seal_manifest.receipt.json and seal_manifest.output.txt. Stop at handback.
'''
(L/'TASK.txt').write_text(task)
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=347063,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),provider='pi',model='spark/DeepSeek-V4.1-Flash-1017',thinking='high',credit=0,accepted_new=58,target_new=80,protected_peers=peers)
save(ROOT/'zeckendorf-formal-r1-ready.json',ready);save(ROOT/'selection-routing-zeckendorf-formal-r1.json',dict(ids=[347063],sources=['https://arxiv.org/abs/2006.16457'],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
print(json.dumps(dict(review_manifest=166,frozen=21,disposition=qr['root_disposition'],next={k:ready[k] for k in ['lane','task_sha256','frozen_bindings']},pdfs=[q.name for q in pdfs],credit=0,accepted_new=58)))
