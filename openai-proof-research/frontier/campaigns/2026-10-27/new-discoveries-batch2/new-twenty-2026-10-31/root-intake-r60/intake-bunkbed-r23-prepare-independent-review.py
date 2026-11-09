"""Root documentary verification of the 382297 literal Lean endpoint lane r23 and preparation of the independent final formal review. No root Lean or mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,shutil,re,zipfile
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');assert led['accepted_new']==57 and led['target_new']==80
F=P/'transitive-bunkbed-endpoint-assembly-formal-deepseek-r23';Q=P/'transitive-bunkbed-primary-qualification-sol-r2';L=P/'transitive-bunkbed-formal-independent-review-claude-r1';assert not L.exists()
pins=read(F/'PINS.json');G6=6*1024**3;G32=32*1024**3;trio={'propext','Classical.choice','Quot.sound'}
def jsonrows(q):
 out=[]
 for line in q.read_text(errors='replace').splitlines():
  try:v=json.loads(line)
  except ValueError:continue
  if isinstance(v,dict):out.append(v)
 return out
def evidence(m,cl,kl):
 c=next(x for x in jsonrows(F/(cl+'.output.txt')) if x.get('stage')=='compile' and x.get('module')==m);k=next(x for x in jsonrows(F/(kl+'.output.txt')) if x.get('stage')=='check' and x.get('module')==m)
 assert c['exit']==k['exit']==0 and read(F/(cl+'.receipt.json'))['exit']==read(F/(kl+'.receipt.json'))['exit']==0,m
 s=sha(F/'src'/(m+'.lean'));o=sha(F/'build'/(m+'.olean'));assert s==c['source_sha256_after']==k['source_sha256_after'] and o==c['olean_sha256_after']==k['olean_sha256_before']==k['olean_sha256_after'],m
 assert c['argv'][0]==pins['lean_bin'] and all(x in c['argv'] for x in ['-j1','-M3500','-DwarningAsError=true']) and k['argv']==[pins['leanchecker_bin'],m] and c['LEAN_NUM_THREADS']==k['LEAN_NUM_THREADS']==1,m
 assert not re.search(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|^\s*axiom\b',(F/'src'/(m+'.lean')).read_text(),re.M),m
 return s,o

# Every documentary check precedes any root mutation.
fex=manifest(F,'MANIFEST.json',248,'seal_manifest','terminal_noncircular_self_exclusions');frozen(F,49)
assert sha(F/'TASK.txt')==read(ROOT/'bunkbed-assembly-r23-ready.json')['task_sha256']
expected={n+'.receipt.json':1 for n in ['end1','model1','probe1','win1']}
frec=[]
for q in sorted(F.glob('*.receipt.json')):
 v=read(q);lean='formal_command.py' in ' '.join(v['command'])
 assert v['cwd']==str(F) and v['cpu_limit_s']==115 and v['group_rss_guard_bytes']==G6 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None,q.name
 assert v['as_limit_bytes']==(G32 if lean else G6),q.name
 assert v['exit']==expected.get(q.name,0),(q.name,v['exit']);frec.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
result=read(F/'results/382297.json');assert result['final_theorem_proven'] is True
base=read(F/'BASELINE.json');order=base['build_order'];assert len(order)==30;want={x['module']:x['source_sha256'] for x in base['modules']}
replayed={}
for m in order:
 s,o=evidence(m,'base_compile_'+m,'base_check_'+m);assert s==want[m],m;replayed[m]=dict(source_sha256=s,olean_sha256=o)
green=result['strict_green_modules'];names={x['name'] for x in green};assert names=={'BunFinalWindow','BunFinalEndpoint','BunFinalModel','BunFinalProbe','AuditFinal'}
finals={}
for row in green:
 s,o=evidence(row['name'],row['compile_label'],row['check_label']);assert s==row['source_sha256'] and o==row['olean_sha256'],row['name'];finals[row['name']]=dict(source_sha256=s,olean_sha256=o)
src=(F/'src/BunFinalEndpoint.lean').read_text();assert re.search(r'open Classical in\n/--[^\n]*-/\ntheorem bunkbed_E7_transitive \(n : Nat\) \(u v : Fin n\) :\n\s+Fintype\.card \{ω : Out n // Reach n ω \(u, false\) \(v, true\)\} ≤\n\s+Fintype\.card \{ω : Out n // Reach n ω \(u, false\) \(v, false\)\} := by',src)
out=(F/'audit_final2.output.txt').read_text(errors='replace');found=dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",out));assert all({y.strip() for y in v.split(',')}<=trio for v in found.values())
assert {y.strip() for y in found['Bun.bunkbed_E7_transitive'].split(',')}==trio and len(found)==10
assert (F/'src/BunkbedBase.lean').read_bytes()==(P/'transitive-bunkbed-new-indicators-formal-pi-r19/src/BunkbedBase.lean').read_bytes()
model=(F/'src/BunFinalModel.lean').read_text();assert 'theorem card_token' in model and 'theorem card_out' in model

fs='382297 LITERAL LEAN ENDPOINT PROVED, uncredited pending independent audit, paper and root adjudication. Root verified from receipts: Bun.bunkbed_E7_transitive, for all n and u v : Fin n, the number of outcomes omega : Out n with Reach n omega (u,false) (v,true) is at most the number with Reach n omega (u,false) (v,false); no added premise; definitions unchanged from BunkbedBase; axioms exactly propext, Classical.choice, Quot.sound. A single replay from an empty build compiled and kernel-checked all thirty chain modules, then three new modules: window factor, endpoint, model checks giving card Token n = n*n and card Out n = 2^(n*n). Four failed compile attempts retained with true exits. Disclosed: a second-command invocation of verify_frozen.py without its argument exited 1 and was rerun correctly, and one read-only python one-liner ran outside the runner. Unpaid: independent formal audit, statement fidelity audit, fresh extracted replay, paper, root adjudication. Credit 0, 57/80. 248 manifest files, 49 frozen bindings.'
fr=dict(utc=now,mathdb_id=382297,source_lane=str(F),manifest_sha256=sha(F/'MANIFEST.json'),verified_manifest_files=248,verified_frozen_bindings=49,chain_replay=replayed,final_modules=finals,axioms=found,runner_receipts=frec,result=result,scientific_summary=fs,root_disposition='LITERAL_ENDPOINT_KERNEL_CHECKED_INDEPENDENT_AUDIT_NEXT',credit=0,accepted_new=57,terminal_self_exclusions=sorted(fex),root_scope='Documentary integrity only; no Lean by root.')
save(P/'transitive-bunkbed-endpoint-assembly-formal-parent-integration-r23.json',fr)
for c in led['candidates']:
 if int(c['mathdb_id'])==382297:c['status']='literal Lean endpoint Bun.bunkbed_E7_transitive kernel-checked (r23), root verified receipts; independent formal audit, paper, fresh replay and root adjudication unpaid; credit 0';c['formal_endpoint']='Bun.bunkbed_E7_transitive'
(P/'ledger.json').write_text(json.dumps(led,indent=2)+'\n')

L.mkdir();origins={}
def copy(src,rel):
 d=L/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,d);assert sha(src)==sha(d);origins[rel]=dict(path=str(src),sha256=sha(src))
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','PINS.json','formal_command.py','run_lean_32g.py','check32.sh','checker32.sh']:copy(F/h,h)
for h in ['check32.sh','checker32.sh']:(L/h).chmod(0o755)
for h in ['registry-roots.json','source_get_guard.py','charge_search.py']:copy(Q/h,h)
save(L/'model-policy.json',read(ROOT/'model-policy-claude-deepseek-20261109.json'))
for d in ['src','build','cache','audit','results','logs','plans','search-responses','sources']:(L/d).mkdir()
final_order=order+['BunFinalWindow','BunFinalEndpoint','BunFinalModel']
(L/'packet').mkdir();zp=L/'packet/382297-source-only.zip'
with zipfile.ZipFile(zp,'w',zipfile.ZIP_DEFLATED) as z:
 for m in sorted(final_order):
  info=zipfile.ZipInfo(f'{m}.lean',date_time=(2026,11,9,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;z.writestr(info,(F/'src'/(m+'.lean')).read_bytes())
save(L/'packet/BUILD-ORDER.json',final_order);save(L/'packet/SOURCE-HASHES.json',{m:sha(F/'src'/(m+'.lean')) for m in final_order})
for q in sorted((Q/'inputs').rglob('*')):
 if q.is_file():copy(q,str(Path('inputs')/q.relative_to(Q/'inputs')))
for rel,q in {'inputs/review-r2-REVIEW.md':Q/'REVIEW.md','inputs/review-r2-PROOF.md':Q/'PROOF.md','inputs/review-r2-review.json':Q/'review.json','inputs/r23-SUMMARY.md':F/'SUMMARY.md','inputs/r23-results.json':F/'results/382297.json','inputs/r23-audit-output.txt':F/'audit_final2.output.txt'}.items():copy(q,rel)
copy(ROOT/'inherited-denials-r564.json','inherited-denials.json')
literal=read(L/'inputs/literal382297.json')
save(L/'reservation.json',dict(ids=[382297],rows=[literal],purpose='Independent final formal review of the 382297 Lean endpoint'));(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n')
save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=4,charged_before_call=True))
save(L/'INPUT-ORIGINS.json',origins)
peers=['expanded-corpus-r531','expanded-corpus-r532']
task=f'''INDEPENDENT FINAL FORMAL REVIEW of MathDB 382297. Claude Opus 5.5, high effort, done personally; no subagents or fallback model. This is a new independent review, not a continuation of the authors. Write ONLY inside {L}. Credit 0; campaign 57 of 80 unchanged. Root alone adjudicates.

THE CLAIM. packet/382297-source-only.zip holds 33 Lean modules, built on Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. They claim:
  theorem Bun.bunkbed_E7_transitive (n : Nat) (u v : Fin n) : Fintype.card {{ω : Out n // Reach n ω (u, false) (v, true)}} ≤ Fintype.card {{ω : Out n // Reach n ω (u, false) (v, false)}}
as the literal statement of MathDB 382297, Hollom's conjecture BBC(E7,T_n) (inputs/literal382297.json; arXiv 2406.01790, Definitions 1.1 to 1.4, Model 4.5, Conjecture 6.4; journal name D7). Try to break it. An honest failure report is the valuable outcome.

FIRST command EXACTLY: timeout 20 python3 -I -B {L}/bootstrap.py
SECOND command EXACTLY: timeout 140 python3 -I -B {L}/verify_frozen.py before

RULES. Peers {peers[0]} and {peers[1]}, every other lane and every author lane are protected: no read, stat, hash, list or glob. Paths inside INPUT-ORIGINS.json are provenance, not permission. No git, installs, accounts, browser, other models, background jobs, or changes to helpers, PINS, packet or inputs. All local non-Lean work goes through: timeout 140 python3 -I -B {L}/run.py UNIQUE_LABEL with Python on stdin. Authored files go through {L}/write_lane.py RELATIVE_PATH with content on stdin. Do not use your own file-reading, editing or web tools on lane files. Let every true exit code stand.
Lean runs only through these wrappers, one at a time, with unique labels:
  {L}/check32.sh MODULE LABEL     compile src/MODULE.lean strictly
  {L}/checker32.sh MODULE LABEL   kernel-check the compiled module
Unchanged limits: 32 GiB address space for Lean only, 6 GiB real memory, CPU 115 s, -j1, -M3500, LEAN_NUM_THREADS 1, -DwarningAsError=true. `import Mathlib` is killed by the memory guard. No unchanged retries.

GATE A: FRESH EXTRACTED REPLAY. Using run.py, extract the zip into the empty src/ directory, rejecting any absolute path, parent reference or symlink, and verify each file against packet/SOURCE-HASHES.json. Then compile and kernel-check all 33 modules in packet/BUILD-ORDER.json from the empty build/ directory, with labels fresh_compile_MODULE and fresh_check_MODULE. Save results/FRESH-REPLAY.json.

GATE B: SOURCE-LEVEL AUDIT. Read every one of the 33 sources yourself. Report any sorry, admit, axiom, unsafe, partial, opaque, implemented_by, extern, native_decide, ofReduceBool, macro, syntax, elab, notation, run_cmd, instance priority trick, redefinition of a mathlib name, or anything else that could change what a statement means. Give a per-module table with its role. Check the chain from each endpoint premise down, and confirm that no theorem is a conclusion-bearing hypothesis.

GATE C: AXIOM AND DEPENDENCY AUDIT. Compile an audit module that prints #print axioms for Bun.bunkbed_E7_transitive and uses Lean's environment API to walk its full transitive constant closure, reporting counts by kind, every axiom, and any unsafe, partial or implemented_by constant. Only propext, Classical.choice and Quot.sound are allowed. If the closure walk cannot fit in the limits, say so and give what you could do.

GATE D: STATEMENT FIDELITY. This is the most important gate. Read src/BunkbedBase.lean against the source definitions in inputs/sources (bunkbed.clean.txt, bunkbed-journal.txt) and against the literal. Check each of: transitive tournament arcs i→j exactly for i<j; two layers; one independent horizontal token per arc per layer; ONE shared bidirectional vertical token per index, not two; the uniform law is exactly the uniform measure on all token assignments, using Bun.card_token and Bun.card_out; Reach is reflexive transitive closure; source in layer false, targets at the same index in each layer; all n and all u, v, including n=0, n=1, v<u and v=u; the direction of the inequality; and that Fintype.card with the classical instance really counts the intended set. Reconcile E7 versus D7 and the zero-length path convention.

GATE E: SEMANTIC CONTROLS IN LEAN. Write and check control modules that prove concrete facts from the definitions, and at least one that would fail if the model were subtly wrong: for example the exact counts at n=1 and u=v=0 (2 and 1 outcomes), a case at n=2 worked out by hand, that the two vertical directions share one token, and that swapping the two counts in the theorem is false for some instance.

GATE F: LIVE PRIOR ART. Two searches and four query strings are allowed, using WebSearch (load it through ToolSearch if deferred, standard mode). Precharge {L}/charge_search.py before each call and save the COMPLETE response through write_lane.py in the very next tool call. Look specifically for any 2024 to 2026 proof or disproof of the bunkbed conjecture for tournaments or D7/E7. inherited-denials.json is binding, and DOI 10.1016/j.ejc.2025.104289 stays closed. Read it in chunks of at most 15000 characters before any network use.

GATE G: SCIENCE. Read inputs/review-r2-PROOF.md, inputs/review-r2-REVIEW.md and inputs/author-CANDIDATE.md. Recheck the short proof independently and give your own view on whether this is routine, with the strongest case on each side. Spot-check the family comparison using inputs/accepted57-scopes.json and inputs/prior39-scopes.json.

DELIVERABLES. FINAL-REVIEW.md, and review.json keyed by "382297" with one result per gate, a list of defects with severity, and one recommendation: TECHNICAL_PASS_ROOT_ADJUDICATION_PENDING or FAIL or HOLD with reasons. Root alone decides acceptance; do not claim credit. Be candid about what you did not check.

SEAL. Run timeout 140 python3 -I -B {L}/verify_frozen.py after, then under run.py with label seal_manifest write MANIFEST.json: a dict with count, credit 0, files as a list of objects with path, sha256 and bytes covering every lane file except the three terminal ones, and terminal_noncircular_self_exclusions listing exactly MANIFEST.json, seal_manifest.receipt.json and seal_manifest.output.txt. Stop at handback.
'''
(L/'TASK.txt').write_text(task)
ff=[q for q in L.rglob('*') if q.is_file() and q.name!='search-budget.json'];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=382297,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),modules=len(final_order),packet_sha256=sha(zp),provider='claudeAgent',model='claude-opus-5-5',effort='high',credit=0,accepted_new=57,target_new=80,protected_peers=peers)
save(ROOT/'bunkbed-independent-review-r1-ready.json',ready);save(ROOT/'selection-routing-bunkbed-independent-review-r1.json',dict(ids=[382297],sources=[literal['source_url']],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
print(json.dumps(dict(r23_manifest=248,frozen=49,replayed=len(replayed),finals=len(finals),axiom_rows=len(found),next={k:ready[k] for k in ['lane','frozen_bindings','modules','packet_sha256','task_sha256']},credit=0,accepted_new=57)))
