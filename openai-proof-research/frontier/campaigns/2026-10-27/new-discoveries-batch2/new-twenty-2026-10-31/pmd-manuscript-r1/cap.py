import os,sys,time,subprocess,resource,json,signal
from pathlib import Path
os.chdir(Path(__file__).resolve().parent)
os.environ.update(MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1',TMPDIR=str(Path.cwd()/'tmp'))
Path('tmp').mkdir(exist_ok=True); Path('receipts').mkdir(exist_ok=True)
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
t=time.monotonic(); p=subprocess.Popen(sys.argv[2:],start_new_session=True); peak=0; reason=None
while p.poll() is None:
 rss=0; cpu=0
 for d in Path('/proc').iterdir():
  if not d.name.isdigit():continue
  try:
   s=(d/'stat').read_text().rsplit(')',1)[1].split()
   if int(s[3])==p.pid:
    rss+=int(s[21])*os.sysconf('SC_PAGE_SIZE');cpu+=(int(s[11])+int(s[12]))/os.sysconf('SC_CLK_TCK')
  except (OSError,ValueError,IndexError):pass
 peak=max(peak,rss)
 if rss>6*1024**3 or cpu>120 or time.monotonic()-t>140:
  reason='resource cap';os.killpg(p.pid,signal.SIGKILL);break
 time.sleep(.05)
rc=p.wait()
Path('receipts',sys.argv[1]+'.json').write_text(json.dumps(dict(command=sys.argv[2:],exit_code=rc,wall_seconds=time.monotonic()-t,sampled_peak_rss_bytes=peak,cpu_cap_seconds=120,wall_cap_seconds=140,rss_cap_bytes=6*1024**3,affinity=sorted(os.sched_getaffinity(0)),reason=reason),indent=2)+'\n')
sys.exit(rc)
