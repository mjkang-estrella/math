import os,sys,resource,subprocess,time,json
os.environ.update(PYTHONDONTWRITEBYTECODE='1',MALLOC_ARENA_MAX='2',OMP_NUM_THREADS='2',OPENBLAS_NUM_THREADS='2',TMPDIR=os.path.dirname(__file__)+'/tmp')
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
t=time.monotonic()
try:r=subprocess.run(sys.argv[1:],preexec_fn=limits,timeout=140);code=r.returncode
except subprocess.TimeoutExpired:code=124
print(json.dumps({'wall_seconds':time.monotonic()-t,'exit':code,'caps':'2 CPUs, 6 GiB AS, CPU 120 s, wall 140 s'}),flush=True);sys.exit(code)
