"""Generic root verification of a final Lean lane and preparation of the independent final formal review. Argument: JSON spec. No root Lean or mathematics."""
import os,resource,sys,subprocess
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,shutil,re,zipfile
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
sp=json.loads(Path(sys.argv[1]).read_text());mid=str(sp['id']);F=P/sp['lane'];Q=P/sp['qual_lane'];L=P/sp['review_lane'];assert not L.exists();V=P/'transitive-bunkbed-formal-independent-review-claude-r1'
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');cur=led['accepted_new'];pins=read(F/'PINS.json');G6=6*1024**3;G32=32*1024**3;trio={'propext','Classical.choice','Quot.sound'}
def jsonrows(q):
 out=[]
 for line in q.read_text(errors='replace').splitlines():
  try:v=json.loads(line)
  except ValueError:continue
  if isinstance(v,dict):out.append(v)
 return out
mc=read(F/'MANIFEST.json')['count'];fex=manifest(F,'MANIFEST.json',mc,'seal_manifest','terminal_noncircular_self_exclusions');rdy=read(ROOT/sp['ready_prev']);frozen(F,rdy['frozen_bindings']);assert sha(F/'TASK.txt')==rdy['task_sha256']
rec=[];failed=[]
for q in sorted(F.glob('*.receipt.json')):
 v=read(q);cmd=' '.join(v['command']);lean='runpy.run_path' in cmd and 'FORMAL_ROOT' in cmd
 assert v['cwd']==str(F) and v['cpu_limit_s']==115 and v['group_rss_guard_bytes']==G6 and v['deadline_s']==130 and len(v['affinity'])<=2 and v.get('killed') is None,q.name
 assert v['as_limit_bytes']==(G32 if lean else G6),q.name
 if v['exit']!=0:failed.append(q.name[:-13])
 rec.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
res=read(F/f'results/{mid}.json');green=res['strict_green_modules'];base=read(F/'BASELINE.json')['immutable_green_modules'];gl=set()
for row in green:
 m=row['name'];cl=row['compile_label'];kl=row['check_label'];gl|={cl,kl}
 c=next(x for x in jsonrows(F/(cl+'.output.txt')) if x.get('stage')=='compile' and x.get('module')==m);k=next(x for x in jsonrows(F/(kl+'.output.txt')) if x.get('stage')=='check' and x.get('module')==m)
 assert c['exit']==k['exit']==0 and read(F/(cl+'.receipt.json'))['exit']==read(F/(kl+'.receipt.json'))['exit']==0,m
 s=sha(F/'src'/(m+'.lean'));o=sha(F/'build'/(m+'.olean'));assert s==row['source_sha256']==c['source_sha256_after']==k['source_sha256_after'] and o==row['olean_sha256']==c['olean_sha256_after']==k['olean_sha256_before']==k['olean_sha256_after'],m
 assert c['argv'][0]==pins['lean_bin'] and all(x in c['argv'] for x in ['-j1','-M3500','-DwarningAsError=true']) and k['argv']==[pins['leanchecker_bin'],m] and c['LEAN_NUM_THREADS']==k['LEAN_NUM_THREADS']==1,m
assert not gl&set(failed)
for row in base:assert sha(F/'src'/(row['name']+'.lean'))==row['source_sha256'] and sha(F/'build'/(row['name']+'.olean'))==row['olean_sha256'],row['name']
names=[x['name'] for x in base]+[x['name'] for x in green]
for m in names:assert not re.search(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|^\s*axiom\b',(F/'src'/(m+'.lean')).read_text(),re.M),m
allax={}
for q in F.glob('*.output.txt'):
 for nm,ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",q.read_text(errors='replace')):allax[nm]=ax
for nm in sp['main_theorems']:assert nm in allax and {y.strip() for y in allax[nm].split(',')}<=trio,nm
srcEnd=(F/'src'/sp['endpoint_module']).read_text() if sp.get('endpoint_module') else ''
for pat in sp.get('statement_regex',[]):assert re.search(pat,srcEnd),pat
head=subprocess.run(['git','-C',pins['packages_root']+'/mathlib','rev-parse','HEAD'],capture_output=True,text=True).stdout.strip();assert head==pins['mathlib_revision']
prod=[m for m in names if 'Audit' not in m and 'Probe' not in m]
deps={m:{x for x in re.findall(r'^import (\S+)',(F/'src'/(m+'.lean')).read_text(),re.M) if x in prod} for m in prod}
order=[];left=dict(deps)
while left:
 ready=sorted(m for m,v in left.items() if v<=set(order));assert ready;order+=ready
 for m in ready:del left[m]
s=Path(sp['summary_file']).read_text().strip()
save(P/sp['integration'],dict(utc=now,mathdb_id=int(mid),source_lane=str(F),manifest_sha256=sha(F/'MANIFEST.json'),verified_manifest_files=mc,verified_frozen_bindings=rdy['frozen_bindings'],baseline_modules=base,green_modules=green,failed_labels=failed,axioms=allax,mathlib_head_verified=head,runner_receipts=rec,result=res,scientific_summary=s,root_disposition='LITERAL_ENDPOINT_KERNEL_CHECKED_INDEPENDENT_AUDIT_NEXT',credit=0,accepted_new=cur,terminal_self_exclusions=sorted(fex),root_scope='Documentary integrity and read-only pin check; no Lean by root.'))
for c in led['candidates']:
 if int(c['mathdb_id'])==int(mid):c['status']='literal Lean endpoint kernel-checked; independent audit, paper and root adjudication pending; credit 0'
led['process_notes'].append(dict(utc=now,item=f'{mid} Lean endpoint verified from receipts; independent audit prepared.'));(P/'ledger.json').write_text(json.dumps(led,indent=2)+'\n')
L.mkdir();origins={}
def copy(src,rel):
 d=L/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,d);assert sha(src)==sha(d);origins[rel]=dict(path=str(src),sha256=sha(src))
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','PINS.json','formal_command.py','run_lean_32g.py','check32.sh','checker32.sh']:copy(F/h,h)
for h in ['check32.sh','checker32.sh']:(L/h).chmod(0o755)
for h in ['registry-roots.json','source_get_guard.py','charge_search.py']:copy(Q/h,h)
save(L/'model-policy.json',read(ROOT/'model-policy-claude-deepseek-20261109.json'))
for d in ['src','build','cache','audit','results','logs','plans','searches','sources']:(L/d).mkdir()
(L/'packet').mkdir();zp=L/f'packet/{mid}-source-only.zip'
with zipfile.ZipFile(zp,'w',zipfile.ZIP_DEFLATED) as z:
 for m in sorted(order):
  info=zipfile.ZipInfo(f'{m}.lean',date_time=(2026,11,9,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;z.writestr(info,(F/'src'/(m+'.lean')).read_bytes())
save(L/'packet/BUILD-ORDER.json',order);save(L/'packet/SOURCE-HASHES.json',{m:sha(F/'src'/(m+'.lean')) for m in order})
for q in sorted((Q/'inputs').rglob('*')):
 if q.is_file():copy(q,str(Path('inputs')/q.relative_to(Q/'inputs')))
for rel,q in {'inputs/qualification-REVIEW.md':Q/'REVIEW.md','inputs/qualification-PROOF.md':Q/'PROOF.md','inputs/lean-SUMMARY.md':F/'SUMMARY.md','inputs/lean-results.json':F/f'results/{mid}.json'}.items():copy(q,rel)
for q in sorted(Q.glob('PROOF-ERRATUM*.md')):copy(q,'inputs/qualification-'+q.name)
for q in sorted((Q/'sources').glob('*.pdf')):copy(q,'inputs/sources/'+q.name)
copy(ROOT/sp['denials'],'inherited-denials.json');literal=read(L/f'inputs/literal{mid}.json');save(L/'reservation.json',dict(ids=[int(mid)],rows=[literal],purpose='Independent final formal review'));(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=4,charged_before_call=True));save(L/'INPUT-ORIGINS.json',origins)
peers=sp['peers'];body=f'''INDEPENDENT FINAL FORMAL REVIEW of MathDB {mid}. Claude Opus 5.5, high effort, done personally; no subagents or fallback model. This is a new independent review; you had no part in the authors' work and must not read their lanes. Write ONLY inside {L}. Credit 0; campaign {cur} of 80 unchanged. Root alone adjudicates.

THE CLAIM. packet/{mid}-source-only.zip holds {len(order)} Lean modules, built on Lean 4.34.1 and mathlib {pins['mathlib_revision']}. {sp['claim']} Try to break it. An honest failure report is the valuable outcome.

FIRST command EXACTLY: timeout 20 python3 -I -B {L}/bootstrap.py
SECOND command EXACTLY: timeout 140 python3 -I -B {L}/verify_frozen.py before

RULES. Peers {peers[0]} and {peers[1]}, every other lane and every author lane are protected: no read, stat, hash, list or glob. Paths in INPUT-ORIGINS.json are provenance, not permission. No git, installs, accounts, browser, other models, background jobs, or changes to helpers, PINS, packet or inputs. All local non-Lean work goes through: timeout 140 python3 -I -B {L}/run.py UNIQUE_LABEL with Python on stdin. Authored files go through {L}/write_lane.py RELATIVE_PATH with content on stdin. Do not use your own file-reading, editing or web tools on lane files, and do not pipe runner output through other commands outside the runner. Let every true exit code stand.
Lean runs only through these wrappers, one at a time, with unique labels:
  {L}/check32.sh MODULE LABEL     compile src/MODULE.lean strictly
  {L}/checker32.sh MODULE LABEL   kernel-check the compiled module
Unchanged limits: 32 GiB address space for Lean only, 6 GiB real memory, CPU 115 s, -j1, -M3500, LEAN_NUM_THREADS 1, -DwarningAsError=true. `import Mathlib` is killed by the memory guard. No unchanged retries.

GATE A: FRESH EXTRACTED REPLAY. Using run.py, extract the zip into the empty src/ directory, rejecting any absolute path, parent reference or symlink, and verify each file against packet/SOURCE-HASHES.json. Then compile and kernel-check all {len(order)} modules in packet/BUILD-ORDER.json from the empty build/ directory, with labels fresh_compile_MODULE and fresh_check_MODULE. Save results/FRESH-REPLAY.json with fields count, all_zero and modules (module, compile_exit, check_exit, olean_sha256).

GATE B: SOURCE-LEVEL AUDIT. Read every source yourself. Report any sorry, admit, axiom, unsafe, partial, opaque, implemented_by, extern, native_decide, ofReduceBool, macro, syntax, elab, notation, run_cmd, instance priority trick, redefinition of a mathlib name, or anything else that could change what a statement means. Give a per-module table with its role, and confirm that no theorem is a conclusion-bearing hypothesis.

GATE C: AXIOM AND DEPENDENCY AUDIT. Compile an audit module with #print axioms for each main theorem ({', '.join(sp['main_theorems'])}) and use Lean's environment API to walk the full transitive constant closure, reporting counts by kind, every axiom, and any unsafe, partial or implemented_by constant. Only propext, Classical.choice and Quot.sound are allowed. If the walk cannot fit in the limits, say so and give what you could do.

GATE D: STATEMENT FIDELITY. This is the most important gate. {sp['fidelity']}

GATE E: SEMANTIC CONTROLS IN LEAN. Write and check control modules that prove concrete facts from the definitions, including at least one that would fail if the model were subtly wrong. {sp['controls']}

GATE F: LIVE PRIOR ART. Two searches and four query strings are allowed, using WebSearch (load it through ToolSearch if deferred, standard mode). Read charge_search.py to see how it is invoked, precharge before each call, and save the COMPLETE response through write_lane.py as the very next tool call, without ending your turn in between. {sp['prior']} inherited-denials.json is binding; read it in chunks of at most 15000 characters before any network use.

GATE G: SCIENCE. Read inputs/qualification-REVIEW.md and inputs/qualification-PROOF.md and give your own view on whether this is routine, with the strongest case on each side. {sp.get('science','')}

DELIVERABLES. FINAL-REVIEW.md, and review.json keyed by "{mid}" with one result per gate named A_fresh_replay, B_source_audit, C_axioms, D_statement_fidelity, E_controls, F_prior_art and G_science, each an object with result and detail, a credit field 0, a list of defects with severity, a field defects_affecting_validity_or_fidelity, and one recommendation: TECHNICAL_PASS_ROOT_ADJUDICATION_PENDING or FAIL or HOLD with reasons. Be candid about what you did not check.

SEAL. Run timeout 140 python3 -I -B {L}/verify_frozen.py after, then under run.py with label seal_manifest write MANIFEST.json: a dict with count, credit 0, files as a list of objects with path, sha256 and bytes covering every lane file except the three terminal ones, and terminal_noncircular_self_exclusions listing exactly MANIFEST.json, seal_manifest.receipt.json and seal_manifest.output.txt. Stop at handback.
'''
(L/'TASK.txt').write_text(body)
ff=[q for q in L.rglob('*') if q.is_file() and q.name!='search-budget.json'];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=int(mid),task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),modules=len(order),packet_sha256=sha(zp),model='claude-opus-5-5',effort='high',credit=0,accepted_new=cur,target_new=80,protected_peers=peers)
save(ROOT/sp['ready_new'],ready);save(ROOT/('selection-routing-'+sp['ready_new']),dict(ids=[int(mid)],sources=[literal['source_url']],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
print(json.dumps(dict(manifest=mc,baseline=len(base),green=len(green),failed=len(failed),order=len(order),mathlib=head[:12],next={k:ready[k] for k in ['lane','frozen_bindings','packet_sha256']})))
