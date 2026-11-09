from pathlib import Path
import os,subprocess,sys,json
r=Path(__file__).resolve().parent.parent
os.chdir(r)
p=json.loads((r/'pins.json').read_text());base=Path(p['cache'])
env=dict(os.environ,PATH='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:/usr/bin:/bin',LEAN_PATH=':'.join([str(r)]+[str(d/'.lake/build/lib/lean') for d in sorted(base.iterdir()) if d.is_dir()]))
sys.exit(subprocess.call([sys.executable,'scripts/capped.py','lean','-j1','-DwarningAsError=true']+sys.argv[1:],env=env))
