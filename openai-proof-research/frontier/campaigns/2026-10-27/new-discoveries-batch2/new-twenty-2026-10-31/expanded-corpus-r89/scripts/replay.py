import pathlib,subprocess,resource,os,time,json,sys,signal,datetime
D=pathlib.Path(__file__).resolve().parents[1]
commands=[('ng-small',['small_graphs.py','6']),('ng-random',['ng_random.py']),('ng-tutte-89101',['ng_tutte.py','89101']),('isolation',['isolation.py']),('isolation-deep',['isolation_deep.py']),('posets',['posets.py','6']),('cubic',['cubic.py']),('lattices',['lattices.py']),('finite-misc',['finite_misc.py']),('bibd-search',['bibd_search.py']),('saturation',['saturation.py']),('flows',['flows.py']),('redei-verification',['redei_verify.py'])]
receipts=[]
def limit():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
 cpus=sorted(os.sched_getaffinity(0));os.sched_setaffinity(0,set(cpus[:2]))
 os.setsid()
for name,args in commands:
 start=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN);path=D/'outputs'/(name+'.replay.log')
 with path.open('w') as f:
  p=subprocess.Popen([sys.executable,str(D/'scripts'/args[0]),*args[1:]],cwd=D,stdout=f,stderr=subprocess.STDOUT,env={**os.environ,'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},preexec_fn=limit)
  try:code=p.wait(timeout=140)
  except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);code=p.wait()
 after=resource.getrusage(resource.RUSAGE_CHILDREN)
 r=dict(name=name,argv=args,returncode=code,wall_seconds=time.monotonic()-start,cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,children_peak_rss_kib_cumulative=after.ru_maxrss,limits=dict(cpu_seconds=120,wall_seconds=140,address_space_bytes=6*1024**3,cpu_affinity_max=2),log=str(path.relative_to(D)))
 receipts.append(r);(D/'receipts/replay.json').write_text(json.dumps(receipts,indent=2)+'\n');print(json.dumps(r),flush=True)
 if code:raise SystemExit(code)
