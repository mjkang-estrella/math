import sys,resource,subprocess,os,pathlib,time,json
L=pathlib.Path(__file__).resolve().parents[1]
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',MALLOC_ARENA_MAX='2',TMPDIR=str(L/'tmp'),HOME=os.environ['HOME'])
t=time.monotonic();name=sys.argv[1]
try:
 with (L/f'logs/{name}.out').open('x') as out:
  r=subprocess.run(sys.argv[2:],stdout=out,stderr=subprocess.STDOUT,env=env,cwd=L,preexec_fn=limits,timeout=140)
 code=r.returncode
except subprocess.TimeoutExpired:code='wall_timeout'
(L/f'logs/{name}.json').write_text(json.dumps({'command':sys.argv[2:],'exit':code,'wall':time.monotonic()-t,'maxrss_children_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'cpu_limit':120,'wall_limit':140,'address_limit_gib':6,'cpus':2},indent=2));print(name,code,round(time.monotonic()-t,2))
