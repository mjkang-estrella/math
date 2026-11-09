from pathlib import Path
import json,subprocess,os,sys
r=Path(__file__).resolve().parent
p=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
l='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
os.environ.update(LEAN_PATH=':'.join([str(r/'formal')]+[str(x/'.lake/build/lib/lean') for x in p.iterdir() if x.is_dir()]),TMPDIR=str(r/'tmp'),MALLOC_ARENA_MAX='2')
sources={p.stem:p for p in (r/'formal').glob('*.lean')};order=[];done=set()
def visit(m):
 if m in done:return
 done.add(m)
 for line in sources[m].read_text().splitlines():
  if line.startswith('import '):
   for dep in line.split()[1:]:
    if dep in sources:visit(dep)
 order.append(m)
for m in sys.argv[1:]:visit(m)
for m in order:
 out=r/'formal'/f'{m}.olean'
 if out.exists():continue
 print(m,flush=True)
 code=subprocess.call([sys.executable,'tools/bounded.py',f'logs/dev-{m}.log',l,'-j1','-DwarningAsError=true','-o',str(out),str(sources[m])])
 if code:sys.exit(code)
