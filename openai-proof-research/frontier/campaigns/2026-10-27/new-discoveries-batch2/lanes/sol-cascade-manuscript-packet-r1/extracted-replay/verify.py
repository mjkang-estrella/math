from pathlib import Path
import os,sys,subprocess,time,json,signal,hashlib,shutil,re
from pin_check import check
b=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(b/'verification').mkdir(exist_ok=True)
(b/'verification/package-audit.json').write_text(json.dumps(check(b),indent=2,sort_keys=True)+'\n')
mods=json.loads((b/'inputs/root-cascade-formal-r1/integrated-core-hashes.json').read_text())['mathematical_modules']
manifest=json.loads((b/'inputs/root-cascade-formal-r1/integrated-core-hashes.json').read_text())['sha256']
for m in mods:assert sha(b/'formal'/f'{m}.lean')==manifest[f'formal/{m}.lean']
out=b/'verification';work=b/'work'
assert not work.exists(),'Use a fresh extraction/directory for each replay'
work.mkdir()
for p in (b/'formal').iterdir():
 if p.suffix=='.lean' or p.name=='run_lean.py':shutil.copyfile(p,work/p.name)
# dependency order derived only from our own source copies
order=[]
def visit(m):
 if m in order:return
 for line in (work/f'{m}.lean').read_text().splitlines():
  if line.startswith('import '):
   for dep in line.split()[1:]:
    if dep in mods:visit(dep)
 order.append(m)
for m in mods:visit(m)
records=[]
for m in order+['OriginAudit']:
 cmd=[sys.executable,'run_lean.py','-j1','-DwarningAsError=true','-DautoImplicit=false','-o',m+'.olean',m+'.lean']
 start=time.monotonic();peak=0;reason=None
 with (out/f'{m}.log').open('w') as f:
  p=subprocess.Popen(cmd,cwd=work,stdout=f,stderr=subprocess.STDOUT,start_new_session=True,env={**os.environ,**{k:'1' for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']}})
  while p.poll() is None:
   rss=0
   for d in Path('/proc').iterdir():
    if d.name.isdigit():
     try:
      st=(d/'stat').read_text().split()
      if int(st[4])==p.pid:rss+=int((d/'status').read_text().split('VmRSS:')[1].split()[0])*1024
     except (OSError,ValueError,IndexError):pass
   peak=max(peak,rss)
   if peak>=3*1024**3 or time.monotonic()-start>=180:
    reason='RSS' if peak>=3*1024**3 else 'wall';os.killpg(p.pid,signal.SIGKILL);p.wait();break
   time.sleep(.05)
 r=dict(module=m,argv=cmd,exit=p.returncode,wall_seconds=time.monotonic()-start,peak_group_RSS=peak,kill=reason);records.append(r);(out/'replay.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(r),flush=True)
 assert p.returncode==0 and reason is None,(m,(out/f'{m}.log').read_text())
txt=(out/'OriginAudit.log').read_text();entries=re.findall(r'^AUDIT (\S+) (\S+)',txt,re.M);assert len(entries)==int(re.search(r'AUDIT_TOTAL (\d+)',txt)[1]);assert {x for x,_ in entries}==set(mods)
assert not re.search(r'FLAGS unsafe=true|axiom=true',txt)
# Record every actually imported source and cached artifact, without using root output.
pins=json.loads((b/'pins.json').read_text());pkgs=[Path(e['path']) for e in pins['packages'].values()];lr=Path(pins['lean_binary']).parents[1];deps={}
for mod in (work/'dependencies.txt').read_text().splitlines():
 rel=Path(*mod.split('.'));src=[work/rel.with_suffix('.lean')]+[p/rel.with_suffix('.lean') for p in pkgs]+[lr/'src/lean'/rel.with_suffix('.lean')]
 found=next((p for p in src if p.exists()),None);assert found is not None,('missing source',mod)
 deps[str(found.relative_to(b)) if found.is_relative_to(b) else str(found)]=sha(found)
 for base in [work]+[p/'.lake/build/lib/lean' for p in pkgs]+[lr/'lib/lean']:
  p=base/rel.with_suffix('.olean')
  if p.exists():
   for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server')]:
    if q.exists():deps[str(q.relative_to(b)) if q.is_relative_to(b) else str(q)]=sha(q)
   break
(out/'dependency-hashes.json').write_text(json.dumps(deps,indent=2,sort_keys=True)+'\n')
(out/'audit-summary.json').write_text(json.dumps({'origin_declarations':len(entries),'per_module':{m:sum(x==m for x,_ in entries) for m in mods},'actual_flags_all_unsafe_false':True,'axioms':'subset of propext Classical.choice Quot.sound','partial_flags':[entry.splitlines()[0] for entry in txt.split('AUDIT ')[1:] if 'FLAGS unsafe=false partial=true axiom=false' in entry],'status':'PASS credit0 pending-final-review'},indent=2)+'\n')
print('PASS exhaustive origin audit',len(entries),flush=True)
