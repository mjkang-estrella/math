import os,resource,subprocess,sys,time,json,pathlib
L=pathlib.Path(__file__).resolve().parents[1]
def pre():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
env=os.environ.copy();env.update(MALLOC_ARENA_MAX='2',OPENBLAS_NUM_THREADS='2',OMP_NUM_THREADS='2',TMPDIR=str(L/'tmp'))
(L/'tmp').mkdir(exist_ok=True);t=time.monotonic()
try:r=subprocess.run(sys.argv[2:],env=env,preexec_fn=pre,timeout=140);code=r.returncode
except subprocess.TimeoutExpired:code=124
print(json.dumps({'command':sys.argv[2:],'wall_seconds':time.monotonic()-t,'exit':code,'usage':list(resource.getrusage(resource.RUSAGE_CHILDREN))}),file=sys.stderr);sys.exit(code)
