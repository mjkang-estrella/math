from pathlib import Path
import os,sys,subprocess,time
root=Path(__file__).resolve().parents[1];os.chdir(root)
lean='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
pkgs=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env=os.environ.copy();env.update(LEAN_PATH=':'.join([str(root/'formal')]+[str(p/'.lake/build/lib/lean') for p in pkgs.iterdir() if (p/'.lake/build/lib/lean').is_dir()]),TMPDIR=str(root/'tmp'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1')
(root/'tmp').mkdir(exist_ok=True)
for m in sys.argv[1:]:
 tag='logs/dev-'+m+'-'+str(time.time_ns())+'.log'
 rc=subprocess.run([sys.executable,'-I','scripts/watchdog.py',tag,lean,'-j1','-DwarningAsError=true','-o','formal/'+m+'.olean','formal/'+m+'.lean'],env=env).returncode
 print((root/(tag)).read_text()[:12000])
 if rc:sys.exit(rc)
