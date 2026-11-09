import os,sys,subprocess,resource,time,signal,json
from pathlib import Path
L=Path(__file__).resolve().parents[1]
def limits():
 os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); os.setsid()
env=dict(os.environ,MALLOC_ARENA_MAX='2',TMPDIR=str(L/'tmp'),PYTHONDONTWRITEBYTECODE='1')
p=subprocess.Popen(sys.argv[1:],preexec_fn=limits,env=env); start=time.monotonic(); peak=0; why=None
while p.poll() is None:
 rss=0
 for q in Path('/proc').iterdir():
  if q.name.isdigit():
   try:
    if os.getpgid(int(q.name))==p.pid:
     rss+=int(next(x.split()[1] for x in (q/'status').read_text().splitlines() if x.startswith('VmRSS:')))*1024
   except (OSError,StopIteration,ProcessLookupError): pass
 peak=max(peak,rss)
 if rss>6*1024**3 or time.monotonic()-start>140:
  why='rss' if rss>6*1024**3 else 'wall'; os.killpg(p.pid,signal.SIGKILL); break
 time.sleep(.2)
r=p.wait(); print(json.dumps({'exit':r,'wall':time.monotonic()-start,'peak_group_rss':peak,'kill':why}),file=sys.stderr); sys.exit(r if r>=0 else 128-r)
