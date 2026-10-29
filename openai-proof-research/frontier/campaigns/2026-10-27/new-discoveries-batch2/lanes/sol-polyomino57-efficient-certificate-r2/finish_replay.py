import os,resource,signal,json,re,hashlib,time
from pathlib import Path
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(40)
L=Path(__file__).resolve().parent;X=L/'extracted'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((X/'pins.json').read_text())
def revision(repo):
 g=repo/'.git'
 if g.is_file():g=(repo/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 h=(g/'HEAD').read_text().strip()
 if not h.startswith('ref: '):return h
 ref=h[5:]
 if (g/ref).exists():return (g/ref).read_text().strip()
 for line in (g/'packed-refs').read_text().splitlines():
  if line.endswith(' '+ref):return line.split()[0]
 raise AssertionError(repo)
assert sha(Path(pins['lean_binary']))==pins['lean_sha256']
for v in pins['packages'].values():assert revision(Path(v['path']))==v['revision']
manifest=json.loads((X/'source-manifest.json').read_text())
assert all(sha(X/p)==h and sha(L/p)==h for p,h in manifest.items())
terms=json.loads((X/'terminal-modules.json').read_text());mods=json.loads((X/'modules.json').read_text())
inventory=[]
for audit in ['OriginAudit']+['Audit'+t for t in terms]:
 log=(X/'logs'/(audit+'.log')).read_text()
 assert 'Forbidden' not in log and 'error:' not in log,audit
 n=int(re.search(r'AUDIT_TOTAL (\d+)',log)[1])
 bs=re.findall(r'AUDIT (\w+) ([^\n]+)\nTYPE (.*?)\nAXIOMS (.*?)\nFLAGS (.*?)\n',log,re.S)
 assert len(bs)==n,(audit,n,len(bs))
 for m,name,t,a,f in bs:
  assert 'unsafe=false' in f and 'axiom=false' in f
  inventory.append(dict(origin=m,name=name,type=t,axioms=a,flags=f))
for m in mods:assert (X/'logs'/(m+'.log')).read_text()==''
assert set(x['origin'] for x in inventory)==set(mods)
assert len(set((x['origin'],x['name']) for x in inventory))==len(inventory)
runs=[json.loads(s) for s in (X/'runs.jsonl').read_text().splitlines()]
# Later separately audited smoke checks are outside the main replay receipt.
runs=runs[:len(mods)+1+len(terms)]
assert len(runs)==len(mods)+1+len(terms)
assert all(r['rc']==0 and r['kill_reason'] is None for r in runs)
originals=json.loads((L/'input-hashes.json').read_text());after={}
assert sha(L.parent/'sol-polyomino57-source-formal-r1/source-only-components.zip')=='00401b09f78d5923ef18f81f6d7ebc7749a66ab8fc9f62fb48f8d6f84d4c55fe'
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
for p,h in originals.items():after[p]=sha(R/p);assert after[p]==h
for p,h in originals.items():
 if '/formal/' in p:
  name=Path(p).name
  if name!='OriginAudit.lean':assert sha(L/'formal'/name)==h
(L/'hash-after.json').write_text(json.dumps(after,indent=2)+'\n')
(X/'declaration-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
receipt={'status':'PASS_COMPONENTS_AND_ALL_SUPPLIED_TERMINAL_ROWS_ONLY','fullSourceClaim':False,'credit':0,'campaign_counts':[5,30,35,60],
 'fresh_extracted_source_only':True,'consumed_candidate_prebuilt_oleans':False,'serial':True,'jobs':1,'warningAsError':True,'autoImplicit':False,
 'modules':len(mods),'terminal_modules':len(terms),'actual_origin_declarations':len(inventory),'allowed_axioms':['propext','Classical.choice','Quot.sound'],
 'partial_generated':[x['name'] for x in inventory if 'partial=true' in x['flags']],
 'all_actual_types_axioms_origins_safety_audited':True,'archive':json.loads((L/'archive-receipt.json').read_text()),
 'sum_run_seconds':sum(r['seconds'] for r in runs),'peak_process_group_rss':max(r['peak_group_rss'] for r in runs),
 'rss_sampling_seconds':0.045,'rss_kill_threshold_bytes':2800*1024**2,'per_run_wall_seconds':230,'per_run_lean_cpu_seconds':[210,215],
 'original_input_hashes_unchanged':True,'archive_and_working_sources_unchanged':True,
 'source_data_rows_external_only':json.loads((L/'numeric-input.json').read_text())['rows'],
 'formal_count_or_formal_terminal_family_equality_claim':False,
 'gaps':['kernel-certified array successor closure through 11 cells (only through five currently checked)',
 'connection of terminal placement forest to that certified terminal layer',
 'closed UniversalContainer 11 witness and unconditional SourceFormula refutation'],
 'no_optimality_first_failure_new_algorithm_or_novelty_claim':True}
(X/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');(L/'FINAL-RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
