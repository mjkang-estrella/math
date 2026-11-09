from pathlib import Path
import subprocess,os,resource,sys,time,json
L=Path(__file__).resolve().parent
name=sys.argv[1];cmd=sys.argv[2:]
def caps():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
env=dict(os.environ,MALLOC_ARENA_MAX='2',OMP_NUM_THREADS='2',OPENBLAS_NUM_THREADS='2',TMPDIR=str(L))
t=time.monotonic()
with (L/(name+'.log')).open('xb') as f:
 try:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=140,env=env,preexec_fn=caps);code=r.returncode
 except subprocess.TimeoutExpired:code='wall_timeout'
(L/(name+'.run.json')).write_text(json.dumps({'command':cmd,'exit':code,'wall_seconds':time.monotonic()-t,'cpu_seconds_limit':120,'address_space_gib':6,'cpus':2},indent=2));print(name,code)
