from pathlib import Path
import os,sys,subprocess
root=Path(__file__).resolve().parents[1]
packages=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
lean='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))}
env.update(LEAN_PATH=':'.join([str(root/'formal'),str(root.parent/'edgepattern-formal-r3/extracted/formal')]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]),MALLOC_ARENA_MAX='2',HOME=str(root/'empty-home'),TMPDIR=str(root/'tmp'),PYTHONDONTWRITEBYTECODE='1')
os.chdir(root)
m=sys.argv[1]
sys.exit(subprocess.run([sys.executable,'-I','scripts/watchdog.py',f'logs/dev-{m}.log',lean,'-j1','-DwarningAsError=true','-o',f'formal/{m}.olean',f'formal/{m}.lean'],env=env).returncode)
