import sys,os,pathlib,subprocess,resource,time,json
P=pathlib.Path(__file__).resolve().parents[1]
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
env=dict(os.environ,MALLOC_ARENA_MAX='2',OPENBLAS_NUM_THREADS='2',OMP_NUM_THREADS='2',TMPDIR=str(P/'inputs'))
name=sys.argv[1];start=time.monotonic()
with (P/'logs'/(name+'.log')).open('x') as f:
 try:
  r=subprocess.run([sys.executable,'-I','-B',str(P/'scripts'/sys.argv[2])]+sys.argv[3:],cwd=P,env=env,preexec_fn=limits,stdout=f,stderr=subprocess.STDOUT,timeout=140);code=r.returncode
 except subprocess.TimeoutExpired:code='wall_timeout'
u=resource.getrusage(resource.RUSAGE_CHILDREN)
(P/'logs'/(name+'-resource.json')).write_text(json.dumps({'exit':code,'wall_seconds':time.monotonic()-start,'maxrss_KiB':u.ru_maxrss,'user_cpu':u.ru_utime,'system_cpu':u.ru_stime,'CPUs':2,'CPU_limit':120,'wall_limit':140,'AS_limit_GiB':6},indent=2))
print(name,code)
