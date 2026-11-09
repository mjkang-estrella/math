from pathlib import Path
import os,sys,subprocess
r=Path(__file__).resolve().parent
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
p=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
os.environ.update(LEAN_PATH=':'.join([str(r/'formal')]+[str(x/'.lake/build/lib/lean') for x in sorted(p.iterdir()) if x.is_dir()]),MALLOC_ARENA_MAX='2',TMPDIR=str(r/'tmp'))
(r/'tmp').mkdir(exist_ok=True)
os.chdir(r)
for m in sys.argv[1:]:
 c=subprocess.call([sys.executable,'-I',str(r/'tools/bounded.py'),str(r/'logs'/f'dev-{m}.log'),str(lean),'-j1','-DwarningAsError=true','-o',f'formal/{m}.olean',f'formal/{m}.lean'])
 print((r/'logs'/f'dev-{m}.log').read_text()[-12000:])
 if c:sys.exit(c)
