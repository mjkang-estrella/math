import os,sys,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[1]
l=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
p=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
e={'PATH':str(l.parent)+':/usr/bin:/bin','HOME':str(r/'home'),'TMPDIR':str(r/'tmp'),'MALLOC_ARENA_MAX':'2','PYTHONDONTWRITEBYTECODE':'1','LEAN_PATH':':'.join([str(r/'formal')]+[str(x/'.lake/build/lib/lean') for x in p.iterdir()])}
m=sys.argv[1]
subprocess.run(['/usr/bin/python3','-I',str(r/'scripts/run_capped.py'),str(r/'logs'/('dev-'+m+'.log')),str(l),'-j1','-DwarningAsError=true','-o',str(r/'formal'/(m+'.olean')),str(r/'formal'/(m+'.lean'))],env=e,cwd=r,check=True)
