import os,sys,time,subprocess,resource,json,signal
from pathlib import Path
D=Path(__file__).resolve().parents[1]
os.environ.update(TMPDIR=str(D/'tmp'),XDG_CACHE_HOME=str(D/'tmp'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1')
def limits():
 os.setsid(); os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
name=sys.argv[1]; start=time.monotonic();p=subprocess.Popen(sys.argv[2:],preexec_fn=limits);peak=0;reason=None
while p.poll() is None:
 rss=0
 for f in Path('/proc').glob('[0-9]*/stat'):
  try:
   s=f.read_text().rsplit(')',1)[1].split()
   if int(s[2])==p.pid:rss+=int(s[21])*os.sysconf('SC_PAGE_SIZE')
  except (OSError,ValueError,IndexError):pass
 peak=max(peak,rss)
 if rss>6*1024**3 or time.monotonic()-start>140:
  reason='resource cap';os.killpg(p.pid,signal.SIGKILL);break
 time.sleep(.1)
rc=p.wait();(D/'receipts'/f'{name}.json').write_text(json.dumps(dict(command=sys.argv[2:],exit=rc,wall_seconds=time.monotonic()-start,sampled_peak_rss_bytes=peak,cpu_limit=120,wall_limit=140,rss_limit=6*1024**3,cpus=2,reason=reason),indent=2)+'\n');sys.exit(rc)
