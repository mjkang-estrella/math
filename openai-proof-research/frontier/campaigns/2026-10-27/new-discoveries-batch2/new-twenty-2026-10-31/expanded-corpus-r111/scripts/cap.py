import os,resource,subprocess,sys,time,pathlib,json
L=pathlib.Path(__file__).resolve().parents[1]; name=sys.argv[1];cmd=sys.argv[2:]
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
a=time.monotonic()
with (L/'logs'/f'{name}.log').open('w') as f:
 try:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=140,preexec_fn=limits,env={**os.environ,'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1','TMPDIR':str(L/'outputs')}); status=r.returncode
 except subprocess.TimeoutExpired:status='wall_timeout'
x={'cmd':cmd,'status':status,'wall_seconds':time.monotonic()-a,'child_usage':list(resource.getrusage(resource.RUSAGE_CHILDREN))};(L/'logs'/f'{name}.json').write_text(json.dumps(x,indent=2));print(x)
