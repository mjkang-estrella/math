import os,sys,subprocess,time,resource,json,signal
from pathlib import Path
root=Path(__file__).resolve().parents[1]
os.environ.update(MALLOC_ARENA_MAX="2",PYTHONDONTWRITEBYTECODE="1",TMPDIR=str(root/"tmp"),XDG_CACHE_HOME=str(root/"tmp"))
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120))
 resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=subprocess.Popen(sys.argv[2:],cwd=root,preexec_fn=limits,start_new_session=True)
t=time.monotonic(); peak=0; violation=None
while p.poll() is None:
 rss=0
 for d in Path('/proc').iterdir():
  if not d.name.isdigit():continue
  try:
   if os.getpgid(int(d.name))==p.pid:
    for line in (d/'status').read_text().splitlines():
     if line.startswith('VmRSS:'):rss+=int(line.split()[1])*1024
  except (OSError,ProcessLookupError):pass
 peak=max(peak,rss)
 if rss>6*1024**3 or time.monotonic()-t>140:
  violation='RSS' if rss>6*1024**3 else 'wall';os.killpg(p.pid,signal.SIGKILL);break
 time.sleep(.05)
code=p.wait()
(root/'receipts'/ (sys.argv[1]+'.json')).write_text(json.dumps(dict(command=sys.argv[2:],returncode=code,wall_seconds=time.monotonic()-t,sampled_peak_rss_bytes=peak,sample_interval_seconds=.05,cpus=sorted(os.sched_getaffinity(0)),cpu_limit_seconds=120,wall_limit_seconds=140,rss_limit_bytes=6*1024**3,MALLOC_ARENA_MAX=2,violation=violation),indent=2)+'\n')
sys.exit(code)
