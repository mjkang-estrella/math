import os,sys,pathlib,subprocess,time,resource,signal,json
L=pathlib.Path(__file__).resolve().parents[1];name=sys.argv[1]
def limits():
 os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
env={**os.environ,'TMPDIR':str(L/'tmp'),'XDG_CACHE_HOME':str(L/'cache'),'HOME':str(L/'cache'),'MALLOC_ARENA_MAX':'2','PYTHONDONTWRITEBYTECODE':'1','OMP_NUM_THREADS':'2','OPENBLAS_NUM_THREADS':'1'}
t=time.monotonic();peak=0;reason=None
with (L/'logs'/f'{name}.log').open('w') as f:
 p=subprocess.Popen(sys.argv[2:],stdout=f,stderr=subprocess.STDOUT,env=env,cwd=L,preexec_fn=limits)
 while p.poll() is None:
  rss=0
  for q in pathlib.Path('/proc').glob('[0-9]*'):
   try:
    if os.getpgid(int(q.name))==p.pid: rss+=int(next(x.split()[1] for x in (q/'status').read_text().splitlines() if x.startswith('VmRSS:')))*1024
   except (OSError,StopIteration):pass
  peak=max(peak,rss)
  if rss>6*1024**3 or time.monotonic()-t>140:
   reason='RSS/wall cap';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.05)
 p.wait()
r={'command':sys.argv[2:],'exit':p.returncode,'wall_s':time.monotonic()-t,'peak_rss':peak,'cap_reason':reason};(L/'logs'/f'{name}.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
