import os,sys,subprocess,time
from pathlib import Path
r=Path(__file__).resolve().parents[1]
lean=Path(os.environ.get('LEAN_BIN','/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'))
pk=Path(os.environ.get('LEAN_PACKAGES','/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'))
e={'PATH':str(lean.parent)+':/usr/bin:/bin','HOME':str(r/'home'),'TMPDIR':str(r/'tmp'),'MALLOC_ARENA_MAX':'2','PYTHONDONTWRITEBYTECODE':'1','LEAN_PATH':':'.join([str(r/'formal')]+[str(x/'.lake/build/lib/lean') for x in pk.iterdir()])}
for mod in sys.argv[1:]:
 label='dev-'+mod+'-'+str(time.time_ns())+'.log'
 p=subprocess.run(['/usr/bin/python3','-I',str(r/'scripts/run_capped.py'),str(r/'logs'/label),str(lean),'-j1','-DwarningAsError=true','-o',str(r/'formal'/(mod+'.olean')),str(r/'formal'/(mod+'.lean'))],env=e,cwd=r)
 if p.returncode:
  print((r/'logs'/label).read_text());sys.exit(p.returncode)
