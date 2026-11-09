import resource,os,sys,subprocess,time,json,pathlib
L=pathlib.Path(__file__).resolve().parents[1]
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
env=os.environ.copy();env.update(PYTHONDONTWRITEBYTECODE='1',MALLOC_ARENA_MAX='2',OPENBLAS_NUM_THREADS='2',OMP_NUM_THREADS='2',TMPDIR=str(L/'tmp'),XDG_CACHE_HOME=str(L/'tmp'))
name=sys.argv[1];t=time.monotonic()
with (L/'outputs'/f'{name}.log').open('x') as f:
 try:r=subprocess.run([sys.executable,'-I',str(L/'scripts'/f'{name}.py')],stdout=f,stderr=subprocess.STDOUT,env=env,preexec_fn=limits,timeout=140);code=r.returncode
 except subprocess.TimeoutExpired:code='wall_timeout'
(L/'outputs'/f'{name}-run.json').write_text(json.dumps({'exit':code,'wall':time.monotonic()-t,'cpu_limit':120,'address_space_gib':6,'cpus':2},indent=2));print(name,code)
