#!/usr/bin/env python3
"""Fresh packet extraction and two bounded Lean runs. External cache required."""
from pathlib import Path,PurePosixPath
import os,sys,resource,subprocess,time,json,zipfile,hashlib,re
O=Path(__file__).resolve().parent
pk=Path(os.environ.get('MATHLIB_PACKAGES','/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'))
lean=os.environ.get('LEAN_BINARY','/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
fresh=O/'work/strict-extracted';fresh.mkdir(parents=True,exist_ok=False)
with zipfile.ZipFile(O/'original/proof-packet.zip') as z:
 seen=set()
 for i in z.infolist():
  p=PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename and i.filename not in seen and i.file_size<10000000 and (i.external_attr>>16)&0o170000 !=0o120000
  seen.add(i.filename); dest=fresh/i.filename;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(z.read(i))
assert (fresh/'FractionalDefect.lean').read_bytes()==(O/'proof/FractionalDefect.lean').read_bytes()
env={'PATH':'/usr/bin:/bin','HOME':str(O/'work/home'),'LANG':'C.UTF-8','LEAN_BINARY':lean,'MATHLIB_PACKAGES':str(pk)}
Path(env['HOME']).mkdir(parents=True,exist_ok=True)
cpus=sorted(os.sched_getaffinity(0))[:2]
def limit():
 os.sched_setaffinity(0,cpus)
 resource.setrlimit(resource.RLIMIT_CPU,(90,95));resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,8*1024**3))
def run(cmd,cwd):
 t=time.monotonic();p=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True,timeout=105,preexec_fn=limit)
 return p,{'command':cmd,'exit_code':p.returncode,'seconds':time.monotonic()-t,'cpus':cpus,'maxrss_children_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'cpu_seconds_soft':90,'cpu_seconds_hard':95,'wall_seconds':105,'address_cap_bytes':8*1024**3}
logs=O/'replay';logs.mkdir(exist_ok=True)
p,r=run([sys.executable,str(fresh/'replay.py')],fresh);(logs/'driver.log').write_text(p.stdout+p.stderr);assert p.returncode==0,p.stderr
for n in ['replay.log','replay-result.json']: (logs/n).write_bytes((fresh/n).read_bytes())
(logs/'driver-result.json').write_text(json.dumps(r,indent=2)+'\n')
env['LEAN_PATH']=':'.join(str(p/'.lake/build/lib/lean') for p in pk.iterdir() if (p/'.lake/build/lib/lean').exists())
audit=O/'reviews/fidelity-evidence/AuditAll.lean';assert audit.read_bytes().startswith((fresh/'FractionalDefect.lean').read_bytes())
p,r=run([lean,'-DwarningAsError=true','-j','1','-M','2048',str(audit)],O);log=p.stdout+p.stderr;(logs/'audit-all.log').write_text(log)
entries=[s for s in log.splitlines() if s.startswith('AUDIT ')]
assert p.returncode==0 and 'AUDIT_TOTAL 32' in log and len(entries)==32
r.update(count=32,pass_all=True,entries=entries,allowed_axioms=['propext','Classical.choice','Quot.sound'],external_cache_trusted=True)
(logs/'declaration-audit.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'replay':json.loads((logs/'replay-result.json').read_text()),'audit_seconds':r['seconds'],'audit_count':32},indent=2))
