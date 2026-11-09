import os,sys,time,subprocess,resource,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
os.chdir(ROOT)
env=os.environ.copy();env.update(MALLOC_ARENA_MAX='2',TMPDIR=str(ROOT/'tmp'),XDG_CACHE_HOME=str(ROOT/'tmp'),PYTHONDONTWRITEBYTECODE='1')
def limits():
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
start=time.monotonic();p=subprocess.Popen(sys.argv[1:],env=env,preexec_fn=limits,start_new_session=True);peak=0;reason=None
while p.poll() is None:
 rss=0
 for f in Path('/proc').glob('[0-9]*/stat'):
  try:
   s=f.read_text().split();
   if int(s[4])==p.pid:rss+=int(s[23])*os.sysconf('SC_PAGE_SIZE')
  except (OSError,ValueError,IndexError):pass
 peak=max(peak,rss)
 if rss>6*1024**3 or time.monotonic()-start>140:
  import signal
  reason='resource cap';os.killpg(p.pid,signal.SIGKILL);break
 time.sleep(.05)
rc=p.wait();receipt={'command':sys.argv[1:],'exit_code':rc,'wall_seconds':time.monotonic()-start,'sampled_peak_group_rss_bytes':peak,'cap_kill':reason,'cpus':2,'cpu_limit_seconds':120,'wall_limit_seconds':140,'rss_limit_bytes':6*1024**3,'malloc_arena_max':2}
(ROOT/'logs'/('cap-'+str(time.time_ns())+'.json')).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));sys.exit(rc)
