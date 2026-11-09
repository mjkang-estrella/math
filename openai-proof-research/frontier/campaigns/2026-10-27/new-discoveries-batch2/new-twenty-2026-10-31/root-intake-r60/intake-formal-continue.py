"""Generic root documentary verification of a formal lane and preparation of its continuation. Arguments: mathdb_id lane next_lane integration_name disposition summary_file task_body_file ready_name ready_file_prefix provider_label peer1 peer2 keep_input_globs(comma). No root Lean or mathematics."""
import os,resource,sys
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,shutil,re
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
mid,lane,nxt,iname,disp,sfile,bodyf,rname,rprev,label,p1,p2,keep=sys.argv[1:14]
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');F=P/lane;L=P/nxt;assert not L.exists()
pins=read(F/'PINS.json');G6=6*1024**3;G32=32*1024**3;trio={'propext','Classical.choice','Quot.sound'}
def jsonrows(q):
 out=[]
 for line in q.read_text(errors='replace').splitlines():
  try:v=json.loads(line)
  except ValueError:continue
  if isinstance(v,dict):out.append(v)
 return out
fex=manifest(F,'MANIFEST.json',read(F/'MANIFEST.json')['count'],'seal_manifest','terminal_noncircular_self_exclusions');rdy=read(ROOT/rprev);frozen(F,rdy['frozen_bindings']);assert sha(F/'TASK.txt')==rdy['task_sha256']
rec=[];failed=[]
for q in sorted(F.glob('*.receipt.json')):
 v=read(q);cmd=' '.join(v['command']);lean='runpy.run_path' in cmd and 'FORMAL_ROOT' in cmd
 assert v['cwd']==str(F) and v['cpu_limit_s']==115 and v['group_rss_guard_bytes']==G6 and v['deadline_s']==130 and len(v['affinity'])<=2,q.name
 assert v['as_limit_bytes']==(G32 if lean else G6),q.name
 if v['exit']!=0:failed.append(q.name[:-13])
 rec.append(dict(path=q.name,sha256=sha(q),exit=v['exit'],killed=v.get('killed')))
res=read(F/f'results/{mid}.json');green=res['strict_green_modules'];greenlabels=set()
for row in green:
 m=row['name'];cl=row['compile_label'];kl=row['check_label'];greenlabels|={cl,kl}
 c=next(x for x in jsonrows(F/(cl+'.output.txt')) if x.get('stage')=='compile' and x.get('module')==m);k=next(x for x in jsonrows(F/(kl+'.output.txt')) if x.get('stage')=='check' and x.get('module')==m)
 assert c['exit']==k['exit']==0 and read(F/(cl+'.receipt.json'))['exit']==read(F/(kl+'.receipt.json'))['exit']==0,m
 s=sha(F/'src'/(m+'.lean'));o=sha(F/'build'/(m+'.olean'));assert s==row['source_sha256']==c['source_sha256_after']==k['source_sha256_after'] and o==row['olean_sha256']==c['olean_sha256_after']==k['olean_sha256_before']==k['olean_sha256_after'],m
 assert c['argv'][0]==pins['lean_bin'] and all(x in c['argv'] for x in ['-j1','-M3500','-DwarningAsError=true']) and k['argv']==[pins['leanchecker_bin'],m] and c['LEAN_NUM_THREADS']==k['LEAN_NUM_THREADS']==1,m
 assert not re.search(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|^\s*axiom\b',(F/'src'/(m+'.lean')).read_text(),re.M),m
assert not greenlabels&set(failed)
audited=0
for lab in {row.get('audit_label') for row in green if row.get('audit_label')}:
 found=re.findall(r"depends on axioms: \[([^\]]*)\]",(F/(lab+'.output.txt')).read_text(errors='replace'));assert found,lab;audited+=len(found);assert all({y.strip() for y in f.split(',')}<=trio for f in found),lab
s=Path(sfile).read_text().strip()
save(P/iname,dict(utc=now,mathdb_id=int(mid),source_lane=str(F),manifest_sha256=sha(F/'MANIFEST.json'),verified_manifest_files=read(F/'MANIFEST.json')['count'],verified_frozen_bindings=rdy['frozen_bindings'],green_modules=green,failed_labels=failed,axiom_rows_audited=audited,runner_receipts=rec,result=res,scientific_summary=s,root_disposition=disp,credit=0,accepted_new=led['accepted_new'],terminal_self_exclusions=sorted(fex),root_scope='Documentary integrity only; no Lean by root.'))
L.mkdir();origins={}
def copy(src,rel):
 d=L/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,d);assert sha(src)==sha(d);origins[rel]=dict(path=str(src),sha256=sha(src))
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','PINS.json','formal_command.py','run_lean_32g.py','check32.sh','checker32.sh']:copy(F/h,h)
for h in ['check32.sh','checker32.sh']:(L/h).chmod(0o755)
save(L/'model-policy.json',read(ROOT/'model-policy-claude-deepseek-20261109.json'))
for d in ['src','build','cache','audit','results','logs']:(L/d).mkdir()
baseline=[]
for row in green:
 m=row['name'];copy(F/'src'/(m+'.lean'),'src/'+m+'.lean');blobs=[]
 for q in sorted((F/'build').glob(m+'.*')):
  if q.is_file():copy(q,'build/'+q.name);blobs.append(dict(path='build/'+q.name,sha256=sha(q)))
 baseline.append(dict(row,blobs=blobs))
for q in sorted((F/'inputs').rglob('*')):
 if q.is_file():copy(q,str(Path('inputs')/q.relative_to(F/'inputs')))
copy(F/'SUMMARY.md','inputs/previous-SUMMARY.md');copy(F/f'results/{mid}.json','inputs/previous-results.json')
for pat in [x for x in keep.split(',') if x]:
 for q in sorted(F.glob(pat)):
  if q.is_file():copy(q,'inputs/previous-drafts/'+q.name)
save(L/'BASELINE.json',dict(origin=str(F),root_verified_manifest_sha256=sha(F/'MANIFEST.json'),immutable_green_modules=baseline,rule='These sources and compiler sidecars are immutable. Import the sealed oleans from build/. Never run check32.sh on these names. New modules must have new names.'))
save(L/'INPUT-ORIGINS.json',origins)
body=Path(bodyf).read_text().replace('{L}',str(L)).replace('{P1}',p1).replace('{P2}',p2)
(L/'TASK.txt').write_text(body)
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=int(mid),task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),baseline_modules=len(baseline),model=label,credit=0,accepted_new=led['accepted_new'],target_new=led['target_new'],protected_peers=[p1,p2])
save(ROOT/rname,ready);save(ROOT/('selection-routing-'+rname),dict(ids=[int(mid)],sources=[],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
print(json.dumps(dict(manifest=read(F/'MANIFEST.json')['count'],green=len(green),failed=len(failed),killed=[r['path'] for r in rec if r['killed']],audited=audited,next={k:ready[k] for k in ['lane','frozen_bindings','baseline_modules']})))
