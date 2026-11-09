import os,sys,subprocess,json,time
from pathlib import Path
L=Path(__file__).resolve().parent.parent
T=L/'extracted';pkg=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
e=os.environ.copy();e.update(TMPDIR=str(L/'tmp'),XDG_CACHE_HOME=str(L/'cache'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1',LEAN_PATH=':'.join([str(T/'build')]+[str(p) for p in sorted(pkg.glob('*/.lake/build/lib/lean'))]))
e['PATH']='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:'+e['PATH']
tag=sys.argv[1]+'-'+str(time.time_ns());args=sys.argv[2:]
cmd=['bash','-c','ulimit -t 120; exec taskset -c 0,1 timeout -k 2 140 /usr/bin/time -v python3 -I "$@"','runner',str(T/'scripts/bounded.py')]+args
with (L/'logs'/f'{tag}.log').open('w') as out,(L/'logs'/f'{tag}.stderr').open('w') as err:r=subprocess.run(cmd,cwd=L,env=e,stdout=out,stderr=err)
(L/'logs'/f'{tag}.result.json').write_text(json.dumps(dict(args=args,exit_code=r.returncode)))
print(tag,r.returncode)
sys.exit(r.returncode)
