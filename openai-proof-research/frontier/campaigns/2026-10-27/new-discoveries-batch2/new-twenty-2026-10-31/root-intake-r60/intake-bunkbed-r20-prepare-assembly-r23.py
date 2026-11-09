"""Root documentary verification of the 382297 Reach bridge lane r20 and preparation of the final Lean assembly lane r23. No root Lean or mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,shutil,re
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');assert led['accepted_new']==57 and led['target_new']==80
F=P/'transitive-bunkbed-reach-formal-deepseek-r20';D=P/'transitive-bunkbed-state-dominance-formal-sol-r22';L=P/'transitive-bunkbed-endpoint-assembly-formal-deepseek-r23';assert not L.exists()
pins=read(F/'PINS.json');G6=6*1024**3;G32=32*1024**3;trio={'propext','Classical.choice','Quot.sound'}
def jsonrows(q):
 out=[]
 for line in q.read_text(errors='replace').splitlines():
  try:v=json.loads(line)
  except ValueError:continue
  if isinstance(v,dict):out.append(v)
 return out

# Every documentary check precedes any root mutation.
fex=manifest(F,'MANIFEST.json',155,'seal_manifest','terminal_noncircular_self_exclusions');frozen(F,36)
assert sha(F/'TASK.txt')==read(ROOT/'bunkbed-deepseek-r20-ready.json')['task_sha256']
expected={n+'.receipt.json':1 for n in ['r20_compile_bridge1','r20_compile_bridge3','r20_compile_fresh1','r20_compile_support1','r20_compile_support2']}
frec=[]
for q in sorted(F.glob('*.receipt.json')):
 v=read(q);lean='formal_command.py' in ' '.join(v['command'])
 assert v['cwd']==str(F) and v['cpu_limit_s']==115 and v['group_rss_guard_bytes']==G6 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None,q.name
 assert v['as_limit_bytes']==(G32 if lean else G6),q.name
 assert v['exit']==expected.get(q.name,0),(q.name,v['exit']);frec.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
result=read(F/'results/382297.json');green=result['strict_green_modules'];assert len(green)==19
for row in green:
 m=row['name'];c=next(x for x in jsonrows(F/(row['compile_label']+'.output.txt')) if x.get('stage')=='compile' and x.get('module')==m);k=next(x for x in jsonrows(F/(row['check_label']+'.output.txt')) if x.get('stage')=='check' and x.get('module')==m)
 assert c['exit']==k['exit']==0 and read(F/(row['compile_label']+'.receipt.json'))['exit']==read(F/(row['check_label']+'.receipt.json'))['exit']==0,m
 s=sha(F/'src'/(m+'.lean'));o=sha(F/'build'/(m+'.olean'));assert s==row['source_sha256']==c['source_sha256_after']==k['source_sha256_after'] and o==row['olean_sha256']==c['olean_sha256_after']==k['olean_sha256_before']==k['olean_sha256_after'],m
 assert c['argv'][0]==pins['lean_bin'] and all(x in c['argv'] for x in ['-j1','-M3500','-DwarningAsError=true']) and k['argv']==[pins['leanchecker_bin'],m] and c['LEAN_NUM_THREADS']==k['LEAN_NUM_THREADS']==1,m
 assert not re.search(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|^\s*axiom\b',(F/'src'/(m+'.lean')).read_text(),re.M),m
audit=(F/'r20_audit_bridge1.output.txt').read_text(errors='replace');found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit);assert len(found)==14 and all({y.strip() for y in f[1].split(',')}<=trio for f in found)
for name in ['Bun.stf_reach_endpoint','Bun.reach_of_lt','Bun.stf_reach_iff','Bun.stf_reach_strong','Bun.reach_self']:assert any(f[0]==name for f in found),name
src=(F/'src/BunReachBridge.lean').read_text();assert re.search(r'theorem stf_reach_endpoint \(n : Nat\) \(u v : Fin n\) \(σ : Bool\) \(ω : Out n\) :\s+\(\(v : Nat\) ∈ sval σ \(stf n \(u : Nat\) \(v : Nat\) \(wres n \(v : Nat\) ω\)\)\) ↔\s+Reach n ω \(u, false\) \(v, σ\)',src)
dg22=read(P/'transitive-bunkbed-state-dominance-formal-parent-integration-r22.json');dgreen={x['name']:x for x in dg22['green_modules']};assert len(dgreen)==28
base=[x['module'] for x in read(F/'BASELINE.json')['modules']];assert len(base)==14
for m in base:assert sha(F/'src'/(m+'.lean'))==sha(D/'src'/(m+'.lean'))==dgreen[m]['source_sha256'],m
chain={m:F/'src'/(m+'.lean') for m in base+['BunReachSupport','BunReachBridge']};chain.update({m:D/'src'/(m+'.lean') for m in dgreen if m.startswith('BunDom')});assert len(chain)==30
deps={m:{x for x in re.findall(r'^import (\S+)',q.read_text(),re.M) if x.startswith('Bun')} for m,q in chain.items()};assert all(v<=set(chain) for v in deps.values())
order=[];left=dict(deps)
while left:
 ready=sorted(m for m,v in left.items() if v<=set(order));assert ready;order+=ready
 for m in ready:del left[m]

fs='382297 uncredited formal r20. Root verified from receipts the literal Reach bridge: Bun.stf_reach_endpoint says that v lies in the layer-sigma state set of the window-v restriction of omega exactly when Reach n omega (u,false) (v,sigma); also Bun.stf_reach_iff, Bun.stf_reach_strong, Bun.reach_of_lt for v<u and Bun.reach_self for v=u, with fourteen audited theorems using only propext, Classical.choice and Quot.sound. Nineteen modules have compile, kernel and hash evidence, including an empty-build replay of the fourteen baseline modules on this lane. Five failed compile attempts retained with true exits. Stopped on root instruction before redundant counting work; BunCountFresh is partial and unused. Both halves now exist. Unpaid: the window-to-outcome count factor, the literal endpoint theorem, a single replay of the whole chain, independent formal audit and paper. Credit 0, 57/80. 155 manifest files, 36 frozen bindings.'
fr=dict(utc=now,mathdb_id=382297,source_lane=str(F),manifest_sha256=sha(F/'MANIFEST.json'),verified_manifest_files=155,verified_frozen_bindings=36,green_modules=green,runner_receipts=frec,result=result,scientific_summary=fs,root_disposition='REACH_BRIDGE_KERNEL_CHECKED_UNCREDITED_ASSEMBLY_NEXT',credit=0,accepted_new=57,terminal_self_exclusions=sorted(fex),root_scope='Documentary integrity only; no Lean by root.')
save(P/'transitive-bunkbed-reach-formal-parent-integration-r20.json',fr)

L.mkdir();origins={}
def copy(src,rel):
 d=L/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,d);assert sha(src)==sha(d);origins[rel]=dict(path=str(src),sha256=sha(src))
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','PINS.json','formal_command.py','run_lean_32g.py','check32.sh','checker32.sh']:copy(F/h,h)
for h in ['check32.sh','checker32.sh']:(L/h).chmod(0o755)
policy=read(ROOT/'model-policy-claude-deepseek-20261109.json');save(L/'model-policy.json',policy)
for d in ['src','build','cache','audit','results','logs']:(L/d).mkdir()
for m,q in chain.items():copy(q,'src/'+m+'.lean')
for rel,q in {'inputs/literal-target.json':F/'inputs/literal-target.json','inputs/shortest-proof-PROOF.md':D/'inputs/shortest-proof-PROOF.md','inputs/r22-SUMMARY.md':D/'SUMMARY.md','inputs/r20-SUMMARY.md':F/'SUMMARY.md','inputs/r20-results.json':F/'results/382297.json','inputs/r22-results.json':D/'results/382297.json'}.items():copy(q,rel)
save(L/'BASELINE.json',dict(build_order=order,modules=[dict(module=m,source_sha256=sha(chain[m]),origin=str(chain[m])) for m in order],rule='These thirty sources are immutable. Rebuild them from empty in build_order. New modules use the prefix BunFinal.'))
save(L/'INPUT-ORIGINS.json',origins)
peers=['expanded-corpus-r530','expanded-corpus-r531']
task=f'''MathDB 382297: final Lean assembly. Pi DeepSeek V4.1 Flash, high thinking. Do the work yourself; no children or fallback model. Write ONLY inside {L}. Credit 0; campaign 57 of 80 unchanged.

TARGET. The bunkbed conjecture in the E7/D7 model for transitive tournaments, with the existing definitions unchanged and no added premise:
  open Classical in
  theorem Bun.bunkbed_E7_transitive (n : Nat) (u v : Fin n) :
    Fintype.card {{ω : Bun.Out n // Bun.Reach n ω (u, false) (v, true)}} ≤ Fintype.card {{ω : Bun.Out n // Bun.Reach n ω (u, false) (v, false)}}

BOTH HALVES ARE ALREADY PROVED and supplied as source in src/:
- Bun.state_endpoint in BunDomFinal: for u ≤ j < n, the count over Bun.Asg n j of j in Bun.sval true (Bun.stf n u j w) is at most the count with Bun.sval false.
- Bun.stf_reach_endpoint in BunReachBridge: (v : Nat) ∈ sval σ (stf n u v (wres n v ω)) ↔ Reach n ω (u,false) (v,σ).
- Bun.reach_of_lt in BunReachBridge: v < u → ¬ Reach n ω (u,false) (v,σ).
wres n j ω is fun t => ω t.1 on Win n j = {{t : Token n // tmax t ≤ j}}, and Asg n j = Win n j → Bool. See inputs/r20-SUMMARY.md and inputs/r22-SUMMARY.md.

FIRST command EXACTLY: timeout 20 python3 -I -B {L}/bootstrap.py
SECOND command EXACTLY: timeout 140 python3 -I -B {L}/verify_frozen.py before

RULES. Peers {peers[0]} and {peers[1]} and every other lane are protected: no read, stat, hash, list or glob. No network, git, installs, accounts, browser, other models, mathematical programs, solvers or background jobs. Do not modify helpers, PINS, inputs or the thirty supplied sources. Authored files go through {L}/write_lane.py RELATIVE_PATH with content on stdin. Non-Lean local work goes through: timeout 140 python3 -I -B {L}/run.py UNIQUE_LABEL with Python on stdin.
Lean runs only through these wrappers, one at a time, each with a unique receipt label:
  {L}/check32.sh MODULE LABEL     compile src/MODULE.lean strictly
  {L}/checker32.sh MODULE LABEL   kernel-check the compiled module
Unchanged: 6 GiB real memory, CPU 115 s, -j1, -M3500, LEAN_NUM_THREADS 1, -DwarningAsError=true. Use specific mathlib imports; `import Mathlib` is killed by the real-memory guard. Do not raise any process limit. No unchanged retries; every changed attempt needs a new label. Keep every failure and its true exit.

STEP 0: WHOLE-CHAIN REPLAY FROM EMPTY. Compile and then kernel-check all thirty modules, in BASELINE.json build_order, from the empty build directory. Labels base_compile_MODULE and base_check_MODULE. This is the first single replay of the two halves together. If one fails, record it exactly, do not edit it, and report it.

STEP 1: WINDOW FACTOR, module BunFinalWindow. For n, j and any predicate P on Asg n j, prove that the number of ω : Out n with P (wres n j ω) equals 2^c times the number of w : Asg n j with P w, where c is the number of tokens outside the window. A natural route is Equiv.piEquivPiSubtypeProd on Out n = Token n → Bool. Use classical decidability throughout.

STEP 2: ENDPOINT, module BunFinalEndpoint. Prove Bun.bunkbed_E7_transitive exactly as stated. If v < u, both sides are empty by reach_of_lt. Otherwise rewrite both sides using stf_reach_endpoint, apply the window factor with j = v, and apply state_endpoint.

STEP 3: MODEL CHECKS, module BunFinalModel. Prove Fintype.card (Bun.Token n) = n * n and Fintype.card (Bun.Out n) = 2 ^ (n * n), and state the probability form: the rational number (count with layer true) / 2^(n*n) is at most (count with layer false) / 2^(n*n). These pin the uniform model to the source's n(n-1)+n tokens.

SUSTAIN. Do not stop at a helper. If blocked, keep the source and diagnostic and try a genuinely different route. A module that compiles but fails its kernel check is NOT green. Never add sorry, admit, axiom, unsafe, native_decide, a weakened target or a conclusion-bearing premise, and do not change any definition.

EVIDENCE. Every new green module needs a passing compile and a passing kernel check. Write AuditFinal.lean with #print axioms for Bun.bunkbed_E7_transitive and each main new theorem, compile it through check32.sh, and keep its output. Only propext, Classical.choice and Quot.sound are allowed. Keep results/382297.json with strict_green_modules (name, source_sha256, olean_sha256, compile_label, check_label, audit_label), exact_final_theorem_statement, final_theorem_proven and an unpaid list. Write SUMMARY.md at the end, honest about anything unproved.

SCIENTIFIC STATUS. A prospective scientific pass is recorded with modest significance and bounded novelty. Acceptance is root-only and still needs an independent formal audit, a paper and a fresh extracted replay. Do not claim credit.

SEAL. Run timeout 140 python3 -I -B {L}/verify_frozen.py after, then under run.py with label seal_manifest write MANIFEST.json: a dict with count, credit 0, files as a list of objects with path, sha256 and bytes covering every lane file except the three terminal ones, and terminal_noncircular_self_exclusions listing exactly MANIFEST.json, seal_manifest.receipt.json and seal_manifest.output.txt. Stop at handback.
'''
(L/'TASK.txt').write_text(task)
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=382297,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),modules=len(order),build_order=order,provider='pi',model='spark/DeepSeek-V4.1-Flash-1017',thinking='high',credit=0,accepted_new=57,target_new=80,protected_peers=peers)
save(ROOT/'bunkbed-assembly-r23-ready.json',ready);save(ROOT/'selection-routing-bunkbed-assembly-r23.json',dict(ids=[382297],sources=['https://arxiv.org/abs/2406.01790'],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
for c in led['candidates']:
 if int(c['mathdb_id'])==382297:c['status']='second adversarial qualification PASS; root prospective scientific pass; Reach bridge (r20) and Bun.state_endpoint (r22) kernel-checked; literal endpoint assembly in progress; replay, formal audit and paper unpaid; credit 0'
(P/'ledger.json').write_text(json.dumps(led,indent=2)+'\n')
print(json.dumps(dict(r20_manifest=155,frozen=36,green=len(green),audited=len(found),next={k:ready[k] for k in ['lane','task_sha256','frozen_bindings','modules']},credit=0,accepted_new=57)))
