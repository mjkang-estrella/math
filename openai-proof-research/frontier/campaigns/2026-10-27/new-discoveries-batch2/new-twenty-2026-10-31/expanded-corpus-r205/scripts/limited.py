import os,resource,subprocess,time,sys,pathlib,json,signal
D=pathlib.Path(sys.argv[1]);name=sys.argv[2]
def pre():
 os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
t=time.monotonic();peak=0;reason=None
with (D/'logs'/f'{name}.log').open('x') as f:
 p=subprocess.Popen(sys.argv[3:],stdout=f,stderr=subprocess.STDOUT,preexec_fn=pre,env={**os.environ,'MALLOC_ARENA_MAX':'2','OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'2','PYTHONDONTWRITEBYTECODE':'1','TMPDIR':str(D/'outputs')})
 while p.poll() is None:
  rss=0
  for x in pathlib.Path('/proc').glob('[0-9]*'):
   try:
    if os.getpgid(int(x.name))==p.pid:rss+=int(next(l.split()[1] for l in (x/'status').read_text().splitlines() if l.startswith('VmRSS:')))*1024
   except (OSError,StopIteration,ProcessLookupError):pass
  peak=max(peak,rss)
  if rss>6*1024**3 or time.monotonic()-t>140:reason='RSS or wall';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.1)
 p.wait()
r={'exit':p.returncode,'wall_seconds':time.monotonic()-t,'process_group_sampled_peak_rss':peak,'kill_reason':reason,'limits':'2 CPUs, 120 CPU seconds, 140 wall seconds, 6 GiB process-group RSS watchdog, MALLOC_ARENA_MAX=2'}
(D/'logs'/f'{name}.json').write_text(json.dumps(r,indent=2));print(r)
