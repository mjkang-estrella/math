import os,sys,subprocess,shutil
from pathlib import Path
r=Path(__file__).resolve().parents[1]
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
pkgs=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(r/'build')]+[str(p/'.lake/build/lib/lean') for p in sorted(pkgs.iterdir()) if p.is_dir()]);env['MALLOC_ARENA_MAX']='2'
name=sys.argv[1];shutil.copyfile(r/'formal'/(name+'.lean'),r/'build'/(name+'.lean'))
log=r/'logs'/(sys.argv[2]+'.log')
sys.exit(subprocess.run([sys.executable,'-I','-B',str(r/'scripts/capped.py'),str(log),str(lean),'-j1','-DwarningAsError=true','-o',name+'.olean',name+'.lean'],cwd=r/'build',env=env).returncode)
