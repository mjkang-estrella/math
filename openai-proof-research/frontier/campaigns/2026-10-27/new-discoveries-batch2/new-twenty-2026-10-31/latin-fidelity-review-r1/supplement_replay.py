from pathlib import Path
import json,subprocess,os,resource,time,zipfile,hashlib
L=Path(__file__).resolve().parent;E=L/'fresh';d=json.loads((L/'dependency-provenance.json').read_text());env=d['environment'];T=Path(env['PATH'].split(':')[0]); receipts=[]
def limits():
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,8*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100))
with zipfile.ZipFile(L/'supplement-packet.zip','w',zipfile.ZIP_DEFLATED) as z:
 for name,p in [('Latin.lean',E/'Latin.lean'),('Supplement.lean',L/'Supplement.lean')]:z.writestr(name,p.read_bytes())
with zipfile.ZipFile(L/'supplement-packet.zip') as z:
 assert set(z.namelist())=={'Latin.lean','Supplement.lean'}
 (E/'Supplement.lean').write_bytes(z.read('Supplement.lean'))
for label,cmd in [('supplement-strict',[str(T/'lean'),'-j1','-DwarningAsError=true','-o','Supplement.olean','Supplement.lean']),('checker-supplement',[str(T/'leanchecker'),'Supplement'])]:
 start=time.monotonic();r=subprocess.run(cmd,cwd=E,env=env,capture_output=True,timeout=110,preexec_fn=limits)
 (L/(label+'.stdout')).write_bytes(r.stdout);(L/(label+'.stderr')).write_bytes(r.stderr)
 receipts.append({'label':label,'command':cmd,'exit_code':r.returncode,'wall_seconds':time.monotonic()-start,'CPU_s':100,'wall_s':110,'AS_bytes':8*1024**3,'cpus':sorted(os.sched_getaffinity(0))[:2]});(L/'supplement-receipts.json').write_text(json.dumps(receipts,indent=2));print(receipts[-1],flush=True)
 assert r.returncode==0
