import os,sys,subprocess,resource,time,json
from pathlib import Path
L=Path(__file__).resolve().parents[1]
def limit():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
env=os.environ.copy();env.update(PYTHONDONTWRITEBYTECODE='1',MALLOC_ARENA_MAX='2',TMPDIR=str(L/'outputs'))
name=sys.argv[1];start=time.time()
with (L/'outputs'/f'{name}.log').open('x') as f:
 try:r=subprocess.run(sys.argv[2:],cwd=L,env=env,preexec_fn=limit,stdout=f,stderr=subprocess.STDOUT,timeout=140);code=r.returncode
 except subprocess.TimeoutExpired:code='wall_timeout'
(L/'outputs'/f'{name}-resource.json').write_text(json.dumps({'command':sys.argv[2:],'returncode':code,'seconds':time.time()-start,'caps':'CPU120 wall140 AS6GiB affinity2'},indent=2))
print(name,code)
