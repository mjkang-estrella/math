from pathlib import Path
import os,subprocess,time,json,hashlib,zipfile
base=Path(__file__).resolve().parent
packet=base.parent/'fresh-corpus-r4/325519-Lean-packet.zip'
dst=base/'strict-extracted';dst.mkdir(exist_ok=True)
zipfile.ZipFile(packet).extractall(dst)
leanbin=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
env=dict(os.environ,LEAN_PATH='.:{}'.format((dst/'leanpath.txt').read_text().strip()),PATH=str(leanbin)+':'+os.environ['PATH'])
cpus=set(sorted(os.sched_getaffinity(0))[:2]); os.sched_setaffinity(0,cpus)
r={'packet_sha256':hashlib.sha256(packet.read_bytes()).hexdigest(),'cpus':sorted(cpus),'mathlib':'d13f23b723b8a846827a245b89c10fc7d3f11612','lean_version':subprocess.check_output([str(leanbin/'lean'),'--version'],text=True),'records':[]}
for m in ['Spectral','Semantics','Endpoint']:
 cmd=[str(leanbin/'lean'),'-DwarningAsError=true','-j2','-o',m+'.olean',m+'.lean']; start=time.monotonic()
 with (dst/(m+'.log')).open('w') as log: p=subprocess.run(cmd,cwd=dst,env=env,stdout=log,stderr=subprocess.STDOUT)
 r['records'].append({'module':m,'command':cmd,'exit_code':p.returncode,'elapsed_seconds':time.monotonic()-start,'log_sha256':hashlib.sha256((dst/(m+'.log')).read_bytes()).hexdigest()})
 if p.returncode: break
r['all_pass']=len(r['records'])==3 and all(x['exit_code']==0 for x in r['records'])
(base/'replay-review.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
