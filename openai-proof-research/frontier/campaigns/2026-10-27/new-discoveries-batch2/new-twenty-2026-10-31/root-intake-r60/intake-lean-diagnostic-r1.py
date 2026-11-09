"""Root documentary verification of the Lean address-space diagnostic; recomputes the pre-set verdict from receipts. No root Lean or mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,re
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');assert led['accepted_new']==57 and led['target_new']==80
L=P/'lean-address-space-diagnostic-sol-r1'
ex=manifest(L,'MANIFEST.json',494,'seal_manifest','terminal_noncircular_self_exclusions');frozen(L,423)
assert sha(L/'TASK.txt')==read(ROOT/'lean-diagnostic-r1-ready.json')['task_sha256']
tg=read(L/'targets.json');kt=tg['kernel_targets'];assert len(kt)==10 and len(tg['compile_targets'])==3
fails={f'a6_{i+1:02d}_{x["module"]}.receipt.json':1 for i,x in enumerate(kt) if x['module'] not in ('URMatchingCanonical','URMatchingRelabelMaxima')}
fails.update({f'b32_compile_{x["module"]}.receipt.json':1 for x in tg['compile_targets']});fails.update({'c32_compile_ProbeFullMathlib.receipt.json':-9,'c32_check_ProbeFullMathlib.receipt.json':1})
assert len(fails)==13
# Local receipt check: the shared helper assumes a 6 GiB cap on every run; this lane deliberately ran 32 GiB on its treatment labels.
rec=[]
for q in sorted(L.glob('*.receipt.json')):
 v=read(q);n=q.name;want32=n[:4] in ('a32_','b32_','c32_')
 assert v['cwd']==str(L) and v['cpu_limit_s']==115 and v['as_limit_bytes']==(32 if want32 else 6)*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2,n
 assert v['killed']==('rss' if n=='c32_compile_ProbeFullMathlib.receipt.json' else None),n
 assert v['exit']==fails.get(n,0),(n,v['exit'])
 rec.append(dict(path=n,sha256=sha(q),exit=v['exit']))
assert len(rec)==32
sig=re.compile(r'failed to read file|bad_alloc|out of memory|failed to create thread')
G6=6*1024**3;G32=32*1024**3;rows=[];both=0;over=False
def rowjson(label):
 for line in (L/(label+'.output.txt')).read_text(errors='replace').splitlines():
  try:v=json.loads(line)
  except ValueError:continue
  if isinstance(v,dict) and v.get('stage') in ('compile','check'):return v
 raise AssertionError(label)
for i,x in enumerate(kt):
 m=x['module'];a=f'a6_{i+1:02d}_{m}';b=f'a32_{i+1:02d}_{m}';ra=read(L/(a+'.receipt.json'));rb=read(L/(b+'.receipt.json'))
 assert ra['as_limit_bytes']==G6 and rb['as_limit_bytes']==G32
 for r in (ra,rb):assert r['group_rss_guard_bytes']==G6 and r['cpu_limit_s']==115 and r['deadline_s']==130 and r['killed'] is None
 for l in (a,b):
  j=rowjson(l);assert j['stage']=='check' and j['module']==m and j['source_sha256_before']==j['source_sha256_after']==x['source_sha256'] and j['olean_sha256_before']==j['olean_sha256_after']==x['olean_sha256']
 ta=(L/(a+'.output.txt')).read_text(errors='replace')+str(ra.get('stderr'));res=bool(sig.search(ta));assert rb['exit']==0
 if ra['exit']!=0:assert res,m;both+=1
 over|=rb['sampled_max_process_vmpeak_bytes']>G6
 rows.append(dict(module=m,chain=x['chain'],control_exit=ra['exit'],control_resource=res,treatment_exit=rb['exit'],treatment_vmpeak=rb['sampled_max_process_vmpeak_bytes'],treatment_rss=rb['sampled_group_rss_peak_bytes']))
assert both==8 and over
c=read(L/'c32_compile_ProbeAlgebra.receipt.json');k=read(L/'c32_check_ProbeAlgebra.receipt.json');f=read(L/'c32_compile_ProbeFullMathlib.receipt.json')
assert c['exit']==k['exit']==0 and c['as_limit_bytes']==k['as_limit_bytes']==G32 and f['killed']=='rss' and f['group_rss_guard_bytes']==G6
s=(L/'src/ProbeAlgebra.lean').read_text();assert not re.search(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|^\s*axiom\b',s,re.M)
assert (L/'VERDICT.md').read_text().startswith('# SUPPORTED')
summary='Lean address-space diagnostic SUPPORTED under the rule fixed in advance; root recomputed it from receipts. Eight of ten previously kernel-blocked modules failed at the 6 GiB address-space cap with resource signatures and passed at 32 GiB with identical source and olean hashes; two passed at both, consistent with sampled VmPeak of about 6.0 to 6.5 GiB sitting right at the old cap. All ten pass at 32 GiB under the unchanged 6 GiB real-memory guard, 115 s CPU and 130 s deadline. A probe importing Complex, Polynomial, Ideal quotients and Real compiled and kernel-checked at under 2 GiB real memory. A probe with import Mathlib was killed by the unchanged 6 GiB real-memory guard, so formal lanes must use specific imports. The three source-only modules fail with ordinary elaboration errors, not resource errors. Infrastructure evidence only: no module becomes green for any candidate, credit 0, 57/80.'
ir=dict(utc=now,source_lane=str(L),manifest_sha256=sha(L/'MANIFEST.json'),verified_manifest_files=494,verified_frozen_bindings=423,runner_receipts=rec,paired_rows=rows,verdict='SUPPORTED',root_recomputed=True,probe=dict(algebra_compile_rss=c['sampled_group_rss_peak_bytes'],algebra_check_rss=k['sampled_group_rss_peak_bytes'],algebra_check_vmpeak=k['sampled_max_process_vmpeak_bytes'],full_mathlib_killed_by='rss',full_mathlib_rss=f['sampled_group_rss_peak_bytes']),scientific_summary=summary,root_disposition='DIAGNOSTIC_SUPPORTED_INFRASTRUCTURE_ONLY',credit=0,accepted_new=57,terminal_self_exclusions=sorted(ex),root_scope='Documentary integrity and recomputation from receipts only; no Lean by root.')
save(P/'lean-address-space-diagnostic-parent-integration-r1.json',ir)
save(ROOT/'lean-cap-policy-20261108.json',dict(utc=now,rule='Formal lanes run Lean compile and kernel checks only through a runner with RLIMIT_AS 32 GiB; all other local work stays at 6 GiB.',runner_source=str(L/'run_lean_32g.py'),runner_sha256=sha(L/'run_lean_32g.py'),check_wrappers=[str(L/'check32.sh'),str(L/'checker32.sh')],unchanged=dict(group_rss_guard_gib=6,cpu_s=115,deadline_s=130,lean_flags=['-j1','-M3500','-DwarningAsError=true'],LEAN_NUM_THREADS=1),import_rule='Use specific mathlib imports; import Mathlib exceeds the 6 GiB real-memory guard.',authority=str(ROOT/'user-decisions-20261108.json'),evidence=str(P/'lean-address-space-diagnostic-parent-integration-r1.json')))
den=read(ROOT/'inherited-denials-r556.json');den['utc']=now;den['root_lean_diagnostic_r1_scope']=summary;save(ROOT/'inherited-denials-r557.json',den)
with (P/'AGENTS.md').open('a') as q:q.write("\nLean diagnostic 2026-11-08: SUPPORTED. Formal lanes run Lean only through the 32 GiB runner recorded in root-intake-r60/lean-cap-policy-20261108.json, with specific mathlib imports; `import Mathlib` exceeds the unchanged 6 GiB real-memory guard.\n")
print(json.dumps(dict(verified=494,frozen=423,control_fail_treat_pass=both,verdict='SUPPORTED',credit=0)))
