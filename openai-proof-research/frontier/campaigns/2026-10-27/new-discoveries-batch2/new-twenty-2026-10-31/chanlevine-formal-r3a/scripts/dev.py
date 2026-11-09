import hashlib, json, os, pathlib, re, subprocess, sys, time, uuid
root=pathlib.Path(__file__).resolve().parent.parent
bin=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
pkg=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
for d in ['logs','tmp','build','cache']: (root/d).mkdir(exist_ok=True)
env=dict(os.environ, PATH=str(bin)+':'+os.environ.get('PATH',''), LEAN_PATH=':'.join([str(root/'build')]+[str(p) for p in sorted(pkg.glob('*/.lake/build/lib/lean'))]),TMPDIR=str(root/'tmp'),XDG_CACHE_HOME=str(root/'cache'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1')
args=sys.argv[1:]
label=pathlib.Path(args[-1]).stem
log=root/'logs'/f'dev-{label}-{time.time_ns()}-{uuid.uuid4().hex[:6]}.log'
with log.open('w') as f:
 p=subprocess.run([sys.executable,'-I',str(root/'scripts/cap.py'),str(bin/'lean'),'-j1','-M3500','-DwarningAsError=true']+args,cwd=root/'formal',env=env,stdout=f,stderr=subprocess.STDOUT)
print(log)
print(log.read_text())
sys.exit(p.returncode)
