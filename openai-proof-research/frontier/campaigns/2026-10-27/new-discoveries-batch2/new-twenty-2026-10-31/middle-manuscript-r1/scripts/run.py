import os,sys,subprocess,time,resource,json,signal
from pathlib import Path
root=Path(__file__).resolve().parent.parent
os.chdir(root)
for d in ['tmp','cache','receipts']: (root/d).mkdir(exist_ok=True)
os.environ.update(MALLOC_ARENA_MAX='2',TMPDIR=str(root/'tmp'),XDG_CACHE_HOME=str(root/'cache'),PYTHONDONTWRITEBYTECODE='1')
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
t=time.monotonic(); peak=0
p=subprocess.Popen(sys.argv[2:],start_new_session=True)
while p.poll() is None:
 rss=0
 for d in Path('/proc').iterdir():
  if d.name.isdigit():
   try:
    if os.getpgid(int(d.name))==p.pid:
     for l in (d/'status').read_text().splitlines():
      if l.startswith('VmRSS:'): rss+=int(l.split()[1])
   except (OSError,ProcessLookupError): pass
 peak=max(peak,rss)
 if rss>6*1024*1024 or time.monotonic()-t>140: os.killpg(p.pid,signal.SIGKILL)
 time.sleep(.05)
code=p.wait()
(root/'receipts'/ (sys.argv[1]+'.json')).write_text(json.dumps(dict(command=sys.argv[2:],exit=code,wall_seconds=time.monotonic()-t,peak_sampled_group_rss_kib=peak,cpus=sorted(os.sched_getaffinity(0)),cpu_limit=120,wall_limit=140,rss_limit_kib=6291456,MALLOC_ARENA_MAX='2'),indent=2)+'\n')
sys.exit(code)
