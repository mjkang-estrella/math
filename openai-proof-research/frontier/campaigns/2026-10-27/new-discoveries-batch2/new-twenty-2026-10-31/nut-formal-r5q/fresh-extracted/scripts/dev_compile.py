import os,json,subprocess,sys
from pathlib import Path
r=Path(__file__).resolve().parents[1]
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
pk=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env={'PATH':str(lean.parent)+':/usr/bin:/bin','HOME':str(r/'home'),'TMPDIR':str(r/'tmp'),'MALLOC_ARENA_MAX':'2','PYTHONDONTWRITEBYTECODE':'1','LEAN_PATH':':'.join([str(r/'formal')]+[str(x/'.lake/build/lib/lean') for x in pk.iterdir()])}
for mod in sys.argv[2:]:
 args=[str(lean),'-j1','-DwarningAsError=true','-o',str(r/'formal'/(mod+'.olean')),str(r/'formal'/(mod+'.lean'))]
 log=r/'logs'/('dev-'+sys.argv[1]+'-'+mod+'.log')
 if log.exists():raise SystemExit('existing log')
 rc=subprocess.run(['/usr/bin/python3','-I',str(r/'scripts/run_capped.py'),str(log)]+args,env=env,cwd=r).returncode
 if rc:raise SystemExit(rc)
