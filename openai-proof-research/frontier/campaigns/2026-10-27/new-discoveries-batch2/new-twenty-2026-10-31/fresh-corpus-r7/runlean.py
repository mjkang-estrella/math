from pathlib import Path
import os,subprocess,resource
p=Path(__file__).parent.resolve();d=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
os.environ['LEAN_PATH']=':'.join(str(x/'.lake/build/lib/lean') for x in d.iterdir() if (x/'.lake/build/lib/lean').exists())
r=subprocess.run(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','-j1','-DwarningAsError=true','Eternal.lean'],cwd=p/'packet',capture_output=True,text=True,timeout=180);(p/'lean.log').write_text(r.stdout+r.stderr);print(r.stdout+r.stderr);print('EXIT',r.returncode)
