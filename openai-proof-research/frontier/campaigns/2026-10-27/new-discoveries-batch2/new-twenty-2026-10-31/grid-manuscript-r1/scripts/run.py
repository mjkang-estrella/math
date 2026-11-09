import os,sys,time,json,subprocess,resource,signal
from pathlib import Path
D=Path(__file__).resolve().parent.parent
os.environ.update(MALLOC_ARENA_MAX='2',TMPDIR=str(D/'tmp'),TMP=str(D/'tmp'),TEMP=str(D/'tmp'),PYTHONDONTWRITEBYTECODE='1',XDG_CACHE_HOME=str(D/'tmp/cache'))
def limits():
 os.setsid(); os.sched_setaffinity(0,{0,1}); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
start=time.monotonic(); p=subprocess.Popen(sys.argv[1:],cwd=D,env=os.environ,preexec_fn=limits); peak=0; killed=None
while p.poll() is None:
 total=0
 for f in Path('/proc').glob('[0-9]*/stat'):
  try:
   z=f.read_text().split(') ',1)[1].split()
   if int(z[2])==p.pid:
    total+=int((f.parent/'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
  except (OSError,ValueError,IndexError): pass
 peak=max(peak,total)
 if total>6*1024**3 or time.monotonic()-start>140:
  killed='RSS' if total>6*1024**3 else 'wall'; os.killpg(p.pid,signal.SIGKILL); break
 time.sleep(.1)
rc=p.wait(); elapsed=time.monotonic()-start
out={'command':sys.argv[1:],'exit_code':rc,'wall_s':elapsed,'sampled_group_peak_rss_bytes':peak,'cpus':[0,1],'cpu_limit_s':120,'wall_limit_s':140,'rss_limit_bytes':6*1024**3,'MALLOC_ARENA_MAX':2,'killed':killed,'sampling_s':.1}
(D/'receipts'/('run-'+str(time.time_ns())+'.json')).write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out)); sys.exit(rc)
