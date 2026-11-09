import os,resource,subprocess,time,sys,pathlib,json,signal
D=pathlib.Path(__file__).resolve().parents[1]
def pre():
 os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
t=time.monotonic();peak=0;reason=None
with (D/'logs'/ (sys.argv[1]+'.log')).open('w') as log:
 p=subprocess.Popen(sys.argv[2:],stdout=log,stderr=subprocess.STDOUT,preexec_fn=pre,env={**os.environ,'MALLOC_ARENA_MAX':'2','PYTHONDONTWRITEBYTECODE':'1','TMPDIR':str(D/'tmp'),'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'2'})
 while p.poll() is None:
  rss=0
  for q in pathlib.Path('/proc').glob('[0-9]*'):
   try:
    if os.getpgid(int(q.name))==p.pid:rss+=int(next(l.split()[1] for l in (q/'status').read_text().splitlines() if l.startswith('VmRSS:')))*1024
   except (OSError,StopIteration,ProcessLookupError):pass
  peak=max(peak,rss)
  if rss>6*1024**3 or time.monotonic()-t>140:reason='RSS/wall cap';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.1)
 p.wait()
r={'returncode':p.returncode,'wall_seconds':time.monotonic()-t,'sampled_group_rss_peak_bytes':peak,'cap_reason':reason,'limits':'2 CPUs; CPU120s/process; wall140s; group RSS6GiB sampled; AS12GiB'}
(D/'logs'/(sys.argv[1]+'.receipt.json')).write_text(json.dumps(r,indent=2));print(r)
