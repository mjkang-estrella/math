import os,sys,time,json,subprocess,resource,signal
from pathlib import Path
root=Path(__file__).resolve().parent.parent
os.chdir(root)
env=os.environ.copy(); env.update(MALLOC_ARENA_MAX='2',TMPDIR=str(root/'tmp'),XDG_CACHE_HOME=str(root/'tmp'),PYTHONDONTWRITEBYTECODE='1',OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1')
label=sys.argv[1]; cmd=sys.argv[2:]
def limits():
 os.setsid(); os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
t=time.monotonic(); peak=0; reason=None
with (root/'logs'/f'{label}.log').open('w') as log:
 p=subprocess.Popen(cmd,env=env,preexec_fn=limits,stdout=log,stderr=subprocess.STDOUT)
 while p.poll() is None:
  rss=0
  for proc in Path('/proc').glob('[0-9]*'):
   try:
    if os.getpgid(int(proc.name))==p.pid:
     rss+=int(next(x.split()[1] for x in (proc/'status').read_text().splitlines() if x.startswith('VmRSS:')))*1024
   except (OSError,ValueError,StopIteration,ProcessLookupError): pass
  peak=max(peak,rss)
  if rss>6*1024**3 or time.monotonic()-t>140:
   reason='RSS or wall cap'; os.killpg(p.pid,signal.SIGKILL); break
  time.sleep(.05)
 p.wait()
r=dict(command=cmd,exit=p.returncode,wall_seconds=time.monotonic()-t,sampled_peak_rss_bytes=peak,sample_seconds=.05,cpu_limit_seconds=120,wall_limit_seconds=140,cpu_count_max=2,rss_limit_bytes=6*1024**3,MALLOC_ARENA_MAX=2,reason=reason,foreground_joined=True)
(root/'receipts'/f'{label}.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));sys.exit(p.returncode)
