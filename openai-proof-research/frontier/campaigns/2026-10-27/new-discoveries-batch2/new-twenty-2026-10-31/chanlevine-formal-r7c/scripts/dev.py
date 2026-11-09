import os,pathlib,subprocess,sys,time
r=pathlib.Path(__file__).resolve().parent.parent
b=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
p=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
e=dict(os.environ,LEAN_PATH=':'.join([str(r/'build')]+[str(x) for x in sorted(p.glob('*/.lake/build/lib/lean'))]),TMPDIR=str(r/'tmp'),XDG_CACHE_HOME=str(r/'cache'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1')
args=([str(b/'lean'),'-j1','-M3500','-DwarningAsError=true','-o',str(r/'build'/f'{sys.argv[1]}.olean'),f'{sys.argv[1]}.lean'] if sys.argv[1]!='check' else [sys.executable,'-I',str(r/'scripts/check_r5.py')])
l=r/'logs'/f'dev-{sys.argv[1]}-{time.time_ns()}.log'
with l.open('w') as f:q=subprocess.run(['/usr/bin/time','-v',sys.executable,'-I',str(r/'scripts/cap.py')]+args,cwd=r/'formal',env=e,stdout=f,stderr=subprocess.STDOUT)
print(l);print(l.read_text());sys.exit(q.returncode)
