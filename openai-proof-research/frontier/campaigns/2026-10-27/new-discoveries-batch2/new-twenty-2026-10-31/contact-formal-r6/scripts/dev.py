import os,sys,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[1]
p=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
l='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
e=os.environ.copy();e['LEAN_PATH']=':'.join([str(r/'work'),str(r.parent/'contact-formal-r5/build')]+[str(x/'.lake/build/lib/lean') for x in sorted(p.iterdir()) if x.is_dir()]);e['MALLOC_ARENA_MAX']='2'
n=sys.argv[1]
subprocess.run([sys.executable,'-I','-B',str(r/'scripts/capped.py'),str(r/'logs'/('dev-'+n+'.log')),l,'-j1','-DwarningAsError=true','-o',str(r/'work'/(n+'.olean')),str(r/'formal'/(n+'.lean'))],env=e,cwd=r/'formal',check=True)
