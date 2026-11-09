"""Root record of the user's 2026-11-08 decisions and target of 80; preparation of the Lean address-space diagnostic lane and target-80 packet tooling. No root Lean or mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,shutil,stat
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
led=read(P/'ledger.json');assert led['accepted_new']==57 and led['target_new']==60
L=P/'lean-address-space-diagnostic-sol-r1';assert not L.exists()

# All documentary checks precede any mutation.
F=P/'high-girth-ur-matching-formal-sol-r8';I=P/'interval-kwidth-formal-sol-r2';K=P/'parking-strong-a2-formal-sol-r1'
g338=read(F/'results/338806.json')['strict_green_modules'];g336=read(I/'results/336276.json')['strict_green_modules'];g323=list(read(K/'results/323531.json')['strict_green_modules'])
assert (len(g338),len(g336),len(g323))==(49,18,3)
chains=[('336276-interval',I,set(g336)),('323531-parking',K,set(g323)),('338806-high-girth',F,set(g338))]
kernel=[];comp=[];seen=set();copies=[]
for name,lane,green in chains:
 mods=sorted(q.stem for q in (lane/'src').glob('*.lean'));ol={q.name[:-6] for q in (lane/'build').glob('*.olean')}
 assert green<=ol
 for m in sorted(ol-green):kernel.append(dict(module=m,chain=name,source_sha256=sha(lane/'src'/(m+'.lean')),olean_sha256=sha(lane/'build'/(m+'.olean'))))
 for m in sorted(set(mods)-ol):comp.append(dict(module=m,chain=name,source_sha256=sha(lane/'src'/(m+'.lean'))))
 for sub in ['src','build']:
  for q in sorted((lane/sub).rglob('*')):
   if q.is_file():
    rel=sub+'/'+str(q.relative_to(lane/sub));assert rel not in seen,rel;seen.add(rel);copies.append((q,rel))
assert len(kernel)==10 and len(comp)==3,(len(kernel),len(comp))
src=(F/'run.py').read_text()
def lim(gib,text):
 a="resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))";assert text.count(a)==2
 text=text.replace(a,f"resource.setrlimit(resource.RLIMIT_AS,({gib}*1024**3,{gib}*1024**3))")
 b="'as_limit_bytes':6*1024**3";assert text.count(b)==1;text=text.replace(b,f"'as_limit_bytes':{gib}*1024**3")
 c="    rss+=int((ent/'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')\n";assert text.count(c)==1
 text=text.replace(c,c+"    vm=max(vm,max([int(l.split()[1])*1024 for l in (ent/'status').read_text().splitlines() if l.startswith('VmPeak:')] or [0]))\n")
 d="peak=0; samples=0; killed=None\n";assert text.count(d)==1;text=text.replace(d,"peak=0; samples=0; killed=None; vm=0\n")
 e="'sampled_group_rss_peak_bytes':peak,";assert text.count(e)==1;text=text.replace(e,e+"'sampled_max_process_vmpeak_bytes':vm,")
 f="lane=pathlib.Path(__file__).resolve().parent\n";assert text.count(f)==1;text=text.replace(f,f+"assert os.environ.get('FORMAL_OPERATION') in ('compile','check') and os.environ.get('FORMAL_MODULE'),'This runner is only for Lean compile and kernel-check runs'\n")
 assert 'rss>6*1024**3' in text and "'group_rss_guard_bytes':6*1024**3" in text
 return text
def wrap(script,run,op):
 o=(F/script).read_text();assert o.count('run.py')==1 and f'FORMAL_OPERATION={op}' in o;return o.replace('run.py',run)

# Lane.
L.mkdir();origins={}
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','model-policy-sol-only.json','PINS.json','formal_command.py']:
 shutil.copyfile(F/h,L/h);assert sha(F/h)==sha(L/h);origins[h]=dict(path=str(F/h),sha256=sha(F/h))
(L/'run_lean_6g.py').write_text(lim(6,src));(L/'run_lean_32g.py').write_text(lim(32,src))
for name,script,run,op in [('checker6.sh','checker.sh','run_lean_6g.py','check'),('checker32.sh','checker.sh','run_lean_32g.py','check'),('check32.sh','check.sh','run_lean_32g.py','compile')]:
 (L/name).write_text(wrap(script,run,op));(L/name).chmod(0o755)
for d in ['results','logs','cache']:(L/d).mkdir()
for q,rel in copies:
 d=L/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,d);assert sha(q)==sha(d);origins[rel]=dict(path=str(q),sha256=sha(q))
save(L/'targets.json',dict(kernel_targets=kernel,compile_targets=comp,order='kernel targets in listed order, then compile targets'))
save(L/'INPUT-ORIGINS.json',origins)
peers=['expanded-corpus-r525','expanded-corpus-r526']
task=f'''LEAN ADDRESS-SPACE DIAGNOSTIC. Uncredited infrastructure test. GPT-6.1 Sol high/default only, no children, no fallback model. Lane: {L}

WHY. Across seven earlier Lean lanes, 37 runs failed with resource-looking errors (failed to read an upstream olean, bad_alloc, INTERNAL PANIC: out of memory, failed to create thread) while sampled real memory stayed under about 1.63 GB. The compiled mathlib files total about 6.1 GB. The hypothesis is that memory-mapping the import closure exhausts the 6 GiB RLIMIT_AS. That is an untested inference. This lane tests it. The user has approved raising RLIMIT_AS from 6 GiB to 32 GiB for Lean compile and kernel-check runs only. Everything else is unchanged: 6 GiB group RSS guard, CPU 115 s, deadline 130 s, -j1, -M3500, LEAN_NUM_THREADS 1, the pinned Lean 4.34.1 and mathlib. Do not raise any other limit.

FIRST command EXACTLY: timeout 20 python3 -I -B {L}/bootstrap.py
SECOND command EXACTLY: timeout 140 python3 -I -B {L}/verify_frozen.py before

Work only inside this lane. Peers {peers[0]} and {peers[1]} and every other lane are protected: no read, stat, hash, list or glob. No network, git, installs, accounts, browser, other models or background jobs. Non-Lean local work goes through: timeout 140 python3 -I -B {L}/run.py UNIQUE_LABEL with Python on stdin. Authored files go through {L}/write_lane.py RELATIVE_PATH with content on stdin. Lean runs go only through the wrappers below, one at a time. Each receipt label is used once.

TEST A: PAIRED KERNEL CHECKS. targets.json lists ten modules that compiled earlier but failed their kernel check, with their source and olean hashes. For each, in order, with NN its two-digit position:
  {L}/checker6.sh MODULE a6_NN_MODULE     (control, 6 GiB)
  {L}/checker32.sh MODULE a32_NN_MODULE   (treatment, 32 GiB)
Each exactly once. Do not edit or recompile these modules. A run that fails is data; do not retry it.

TEST B: COMPILE. targets.json lists three modules that have source but no olean. For each: {L}/check32.sh MODULE b32_compile_MODULE . If that exits 0, run {L}/checker32.sh MODULE b32_check_MODULE . These may fail for ordinary reasons such as elaboration errors or low stack, and that is an honest outcome. Distinguish it from a resource failure.

TEST C: PROBES OF WHAT FUTURE WORK NEEDS. Write two small new modules in src/ with write_lane.py. ProbeAlgebra imports specific current mathlib modules giving Complex, Polynomial, Ideal quotients, Real and norm_num, and proves one trivial genuine statement that uses each area. ProbeFullMathlib has `import Mathlib` and one trivial theorem over the reals. For each: check32.sh then checker32.sh, labels c32_compile_NAME and c32_check_NAME. If an import name is wrong you may correct it and use a new label. Record each attempt.

RESOURCE SIGNATURE means the output or stderr contains: failed to read file, bad_alloc, out of memory, failed to create thread, or the receipt shows killed. A kernel rejection of a declaration or an elaboration error is NOT a resource failure; report it exactly.

ANALYSIS. Write results/diagnostic.json with one row per run: test, module, chain, cap_gib, label, exit, killed, kind (pass, resource, other), the resource file named if any, wall_s, sampled_group_rss_peak_bytes, sampled_max_process_vmpeak_bytes, olean_sha256_before and after. Also write VERDICT.md, using this rule fixed in advance:
SUPPORTED: at least three Test A modules fail the 6 GiB control with a resource signature and exit 0 at 32 GiB, and at least one passing run shows VmPeak above 6 GiB.
PARTIAL: some Test A modules clear at 32 GiB but at least one still fails at 32 GiB with a resource signature.
NOT SUPPORTED: no module clears, or the controls mostly pass at 6 GiB.
State the verdict and any control that unexpectedly passed, since earlier failures varied in which file they named. Also say plainly from Test C whether Complex, Polynomial, Ideal and full-Mathlib imports now check within the unchanged 6 GiB real-memory guard and CPU limit, and give peak RSS and CPU time, because future candidates depend on it.

SCOPE. This is infrastructure evidence only. Credit 0, campaign 57 of 80 unchanged. A pass here does not make any module green for any candidate. By user ruling 323531 is excluded with no credit and 338806 stays on hold; 336276 is excluded as routine. Do not develop mathematics for them.

SEAL. Run timeout 140 python3 -I -B {L}/verify_frozen.py after, then under run.py with label seal_manifest write MANIFEST.json: a dict with count, credit 0, files as a list of objects with path, sha256 and bytes covering every file in the lane except the three terminal ones, and terminal_noncircular_self_exclusions listing exactly MANIFEST.json, seal_manifest.receipt.json and seal_manifest.output.txt. Stop at handback with the verdict and the Test C answer. Do not start other work.
'''
(L/'TASK.txt').write_text(task)
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),kernel_targets=[x['module'] for x in kernel],compile_targets=[x['module'] for x in comp],model='gpt-6.1-sol',reasoning='high',service='default',credit=0,accepted_new=57,target_new=80,protected_peers=peers,as_cap_control_gib=6,as_cap_treatment_gib=32,rss_guard_gib=6)
save(ROOT/'lean-diagnostic-r1-ready.json',ready);save(ROOT/'selection-routing-lean-diagnostic-r1.json',dict(ids=[338806,336276,323531],sources=[],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))

# Decisions, denials, ledger and campaign rules.
dec=dict(utc=now,raw_user_reply='1. yes / 2. keep progress / 3. no / 4. hold / let\'s go for 80',decisions={'lean_address_space':'Raise RLIMIT_AS from 6 GiB to 32 GiB for Lean compile and kernel-check runs only; RSS, CPU and deadline caps unchanged. First re-run the blocked checks unchanged.','discovery':'Keep progress: discovery rounds continue.','323531':'No: not credited, and the closed 2014 and 2017 final versions stay closed.','338806':'Hold: remains on scientific hold with no credit.','target':'Target raised from 60 to 80 new accepted results beyond 39 prior.'},accepted_new=57,target_new=80)
save(ROOT/'user-decisions-20261108.json',dec)
scope='USER DECISIONS 2026-11-08, binding. Target is now 80 new accepted results beyond 39 prior; 57/80, 96 total. MathDB 323531 is excluded by user significance ruling, credit 0; arXiv 1205.4293 and its 2014 final, and arXiv 1504.06869 and its 2017 final, stay closed to all new deliveries. MathDB 338806 stays on scientific hold, credit 0. The Lean address-space cap for compile and kernel-check runs only is authorized at 32 GiB and is being tested in a protected diagnostic lane; discovery lanes still run no Lean. All other caps, source-access rules and the credit standard are unchanged.'
den=read(ROOT/'inherited-denials-r555.json');den['utc']=now;den['root_user_decisions_20261108_scope']=scope;save(ROOT/'inherited-denials-r556.json',den)
led['target_new']=80;led['target']=80;led['status']='active_research_57_of_80_accepted'
led['target_history'].append(dict(utc=now,target=80,instruction="let's go for 80 (user, 2026-11-08, after 57 accepted)"))
led['excluded_after_review']['323531']='parking-strong-a2-qualification-parent-integration-r2.json: ordinary and literal PASS; user significance ruling 2026-11-08 no credit, closed finals stay closed'
led['user_decisions_20261108']=dec;led['process_notes'].append(dict(utc=now,item='User decisions recorded in root-intake-r60/user-decisions-20261108.json; Lean diagnostic prepared; discovery continues toward 80.'))
(P/'ledger.json').write_text(json.dumps(led,indent=2)+'\n')
with (P/'AGENTS.md').open('a') as f:f.write("\n\n## Latest user steering (2026-11-08): extend to eighty\n\nAfter 57 acceptances the user asked to \"go for 80\". The campaign target is now EIGHTY new accepted solutions beyond the 39 prior results. All requirements above, including the literal Lean endpoint and the substantive credit standard, are unchanged. All subagent work uses GPT-6.1 Sol at high effort and default speed only (user, 2026-11-07), which supersedes the Pi/GLM and Claude allocations above; the three-delegate cap stands. MathDB 323531 is excluded by user ruling and its closed final versions stay closed. MathDB 338806 stays on hold. RLIMIT_AS for Lean compile and kernel-check runs only may be 32 GiB; real-memory, CPU and deadline caps are unchanged.\n")

# Target-80 packet tooling: the pinned constructor with only the target and selector binding changed.
old=(ROOT/'prepare_discovery_packet_soft_asymp.py').read_text();assert sha(ROOT/'prepare_discovery_packet_soft_asymp.py')=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b'
reps=[("assert ledger['target_new']==60 and","assert ledger['target_new']==80 and"),(".replace('55/60',f'{current}/60')",".replace('55/60',f'{current}/80')"),("repr(f'Current{current}/60 beyond39 prior,{current+39}total.')","repr(f'Current{current}/80 beyond39 prior,{current+39}total.')"),("+f'{current}/60 beyond39 prior,{current+39}total.","+f'{current}/80 beyond39 prior,{current+39}total."),("target_new=60,model=","target_new=80,model="),
("selector=ROOT/'reserve-discrete-soft-asymp-20261108-r503.py';assert sha(selector)=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'","selector=Path(config['metadata_selector']);assert selector.parent==ROOT and sha(selector)==config['metadata_selector_sha256']"),
("tail=tail.replace('reserve-finite-flagship-later-20261107-r390.py','reserve-discrete-soft-asymp-20261108-r503.py')","tail=tail.replace('reserve-finite-flagship-later-20261107-r390.py',selector.name)")]
new=old
for a,b in reps:
 assert new.count(a)==1,a;new=new.replace(a,b)
save_text=ROOT/'prepare_discovery_packet_target80.py';assert not save_text.exists();save_text.write_text('# Root 2026-11-08: pinned soft-asymp constructor with target 80 and a config-pinned selector; nothing else changed.\n'+new)
sel=(ROOT/'reserve-discrete-soft-asymp-20261108-r503.py').read_text()
a="def disc(d):\n    s = ' '.join(d.get('tags') or []).lower()\n    return any(k in s for k in DISC if k != 'spectral')\n";assert sel.count(a)==1
b='''BROAD = ('number-theory','finite-fields','group-theory','finite-groups','commutative-algebra','symmetric-functions','convex-geometry','discrete-geometry','semigroup','ring-theory','linear-algebra','matrix','polynomial')
DEEP = ('analytic-number','automorphic','l-function','modular-form','elliptic-curve','arithmetic-geometry','algebraic-geometry','birational','derived','moduli','mirror','symplectic','3-manifold','knot','quantum-group','operator-algebra','riemannian','ergodic','abelian-variet','hyperbolic','complex-geometry','representation-theory','dynamical','topology','harmonic-analysis','spectral-theory','model-theory','singularit','cluster-algebra','geometric-group')
def disc(d):
    tags = [t.lower() for t in d.get('tags') or []]
    s = ' '.join(tags); st = d.get('statement') or ''
    if any(k in s for k in DISC if k != 'spectral') or any(x in s for x in DEEP): return False
    return any(x in s for x in BROAD) and not ASYMP.search(st) and not ASYMP.search(d.get('title') or '') and sum(bool(p.search(st)) for p in FIN) >= 2
'''
sel='# ROOT 2026-11-08 METADATA-ONLY BROADENING for r526: outside the discrete tags, admit elementary number theory and finite algebra with non-asymptotic statements and at least two finite-instance cues; deep-area tags are excluded. Not scientific review or clearance.\n'+sel.replace(a,b)
(ROOT/'reserve-broadened-finite-algebra-20261108-r526.py').write_text(sel)
print(json.dumps(dict(ready=ready,constructor_sha=sha(save_text),selector_sha=sha(ROOT/'reserve-broadened-finite-algebra-20261108-r526.py'))))
