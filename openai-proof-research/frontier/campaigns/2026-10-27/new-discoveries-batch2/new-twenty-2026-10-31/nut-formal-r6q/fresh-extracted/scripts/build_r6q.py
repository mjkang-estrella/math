"""Sequential resumable development build; every attempt has a unique log."""
import os,sys,json,subprocess,hashlib,time
from pathlib import Path
r=Path(__file__).resolve().parents[1]
lean=Path(os.environ.get('LEAN_BIN','/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'))
pk=Path(os.environ.get('LEAN_PACKAGES','/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'))
env={'PATH':str(lean.parent)+':/usr/bin:/bin','HOME':str(r/'home'),'TMPDIR':str(r/'tmp'),'MALLOC_ARENA_MAX':'2','PYTHONDONTWRITEBYTECODE':'1','LEAN_PATH':':'.join([str(r/'formal'),str(r.parent/'nut-formal-r5q/formal')]+[str(x/'.lake/build/lib/lean') for x in pk.iterdir()])}
mods=json.loads((r/'new-certificate-modules.json').read_text())+json.loads((r/'support-modules.json').read_text())+['PerSupport']
statefile=r/'development-build.json';state=json.loads(statefile.read_text()) if statefile.exists() else {}
for idx,m in enumerate(mods):
 src=r/'formal'/(m+'.lean');h=hashlib.sha256(src.read_bytes()).hexdigest()
 if state.get(m,{}).get('sha256')==h and (r/'formal'/(m+'.olean')).exists():continue
 log=r/'logs'/f'build-{time.time_ns()}-{m}.log'
 rc=subprocess.run(['/usr/bin/python3','-I',str(r/'scripts/capped_r6q.py'),str(log),str(lean),'-j1','-DwarningAsError=true','-o',str(r/'formal'/(m+'.olean')),str(src)],env=env,cwd=r).returncode
 if rc:
  print(log.read_text()[-10000:],flush=True);raise SystemExit(rc)
 state[m]={'sha256':h,'receipt':str(log.with_suffix('.log.json').relative_to(r))};statefile.write_text(json.dumps(state,indent=2)+'\n')
 print(f'PROGRESS {idx+1}/{len(mods)} {m}',flush=True)
