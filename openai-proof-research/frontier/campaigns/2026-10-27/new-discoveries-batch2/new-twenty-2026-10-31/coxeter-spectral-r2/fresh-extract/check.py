from pathlib import Path
import os,subprocess,time,sys,json
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
w=Path(__file__).resolve().parent;pk=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages');env=os.environ.copy();env['LEAN_PATH']=':'.join(str(p/'.lake/build/lib/lean') for p in pk.iterdir());t=time.monotonic();f=sys.argv[1];cmd=['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','-j2','-M3500','-DwarningAsError=true',f]
try:
 r=subprocess.run(cmd,cwd=w,env=env,capture_output=True,text=True,timeout=180);s=r.stdout+r.stderr;code=r.returncode
except subprocess.TimeoutExpired as e:s=(e.stdout or b'').decode()+'\nTIMEOUT';code=124
(w/(f+'.log')).write_text(s);(w/(f+'.receipt.json')).write_text(json.dumps(dict(command=cmd,exit_code=code,elapsed=time.monotonic()-t),indent=2));print(code,s[:5000])

sys.exit(code)
