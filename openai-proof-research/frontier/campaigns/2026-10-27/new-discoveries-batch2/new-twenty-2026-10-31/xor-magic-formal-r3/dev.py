from pathlib import Path
import os,sys,subprocess
r=Path(__file__).resolve().parent
p=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
l='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
os.environ.update(LEAN_PATH=':'.join([str(r/'formal'),str(r.parent/'xor-magic-formal-r2/formal')]+[str(x/'.lake/build/lib/lean') for x in p.iterdir() if x.is_dir()]),TMPDIR=str(r/'tmp'),MALLOC_ARENA_MAX='2')
(r/'tmp').mkdir(exist_ok=True)
m=sys.argv[1]
sys.exit(subprocess.call([sys.executable,'tools/bounded.py',f'logs/dev-{m}.log',l,'-j1','-DwarningAsError=true','-o',f'formal/{m}.olean',f'formal/{m}.lean']))
