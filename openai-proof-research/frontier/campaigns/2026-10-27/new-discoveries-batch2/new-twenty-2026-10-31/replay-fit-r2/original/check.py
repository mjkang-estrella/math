from pathlib import Path
import os, subprocess, sys, time, json
w=Path(__file__).resolve().parent
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
pk=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
e=os.environ.copy();e['LEAN_PATH']=':'.join([str(w)]+[str(p/'.lake/build/lib/lean') for p in pk.iterdir()])
f=sys.argv[1]; cmd=['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','-j2','-M3500','-DwarningAsError=true','-o',str(w/(Path(f).stem+'.olean')),f]
t=time.monotonic();r=subprocess.run(cmd,cwd=w,env=e,capture_output=True,text=True,timeout=300)
s=r.stdout+r.stderr;(w/(f+'.log')).write_text(s);(w/(f+'.receipt.json')).write_text(json.dumps(dict(command=cmd,exit_code=r.returncode,elapsed=time.monotonic()-t),indent=2));print(s);sys.exit(r.returncode)
