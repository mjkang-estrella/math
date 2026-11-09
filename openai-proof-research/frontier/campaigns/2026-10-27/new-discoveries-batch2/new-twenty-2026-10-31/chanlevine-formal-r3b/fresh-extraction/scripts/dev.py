from pathlib import Path
import os,sys,subprocess,time
r=Path(__file__).resolve().parent.parent
b=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
p=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
e=dict(os.environ,LEAN_PATH=':'.join([str(r/'build')]+[str(x) for x in sorted(p.glob('*/.lake/build/lib/lean'))]),TMPDIR=str(r/'tmp'),XDG_CACHE_HOME=str(r/'cache'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1')
for m in sys.argv[1:]:
 l=r/'logs'/f'dev-{m}-{time.time_ns()}.log'
 with l.open('w') as f:
  z=subprocess.run([sys.executable,'-I',str(r/'scripts/cap.py'),str(b/'lean'),'-j1','-M3500','-DwarningAsError=true','-o',str(r/'build'/f'{m}.olean'),f'{m}.lean'],cwd=r/'formal',env=e,stdout=f,stderr=subprocess.STDOUT)
 print(l,flush=True);print(l.read_text(),flush=True)
 if z.returncode:sys.exit(z.returncode)
