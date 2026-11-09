import os,sys,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[1]
lean=Path(os.environ.get('LEAN_BIN','/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'))
pk=Path(os.environ.get('LEAN_PACKAGES','/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'))
env={'PATH':str(lean.parent)+':/usr/bin:/bin','HOME':str(r/'home'),'TMPDIR':str(r/'tmp'),'MALLOC_ARENA_MAX':'2','PYTHONDONTWRITEBYTECODE':'1','LEAN_PATH':':'.join([str(r/'formal'),str(r.parent/'nut-formal-r5q/formal')]+[str(x/'.lake/build/lib/lean') for x in pk.iterdir()])}
for mod in sys.argv[2:]:
 log=r/'logs'/('dev-'+sys.argv[1]+'-'+mod+'.log')
 if log.exists():raise SystemExit('existing log')
 rc=subprocess.run(['/usr/bin/python3','-I',str(r/'scripts/capped_r6q.py'),str(log),str(lean),'-j1','-DwarningAsError=true','-o',str(r/'formal'/(mod+'.olean')),str(r/'formal'/(mod+'.lean'))],env=env,cwd=r).returncode
 print(log.read_text()[-12000:])
 if rc:raise SystemExit(rc)
