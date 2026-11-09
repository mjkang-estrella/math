import os,sys,resource,subprocess,time,json,pathlib,signal
D=pathlib.Path(__file__).resolve().parents[1]
cmd=sys.argv[2:]; tag=sys.argv[1]+'-'+str(time.time_ns())
def cap():
 os.setsid(); os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
env=os.environ.copy();env.update(MALLOC_ARENA_MAX='2',TMPDIR=str(D/'tmp'),XDG_CACHE_HOME=str(D/'cache'),PYTHONDONTWRITEBYTECODE='1')
t=time.monotonic()
with (D/'logs'/f'{tag}.log').open('w') as log:
 p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,env=env,preexec_fn=cap)
 peak=0;reason=None
 while p.poll() is None:
  rss=0
  for stat in pathlib.Path('/proc').glob('[0-9]*/stat'):
   try:
    vals=stat.read_text().rsplit(')',1)[1].split()
    if int(vals[2])==p.pid:rss+=int(vals[21])*os.sysconf('SC_PAGE_SIZE')
   except (OSError,ValueError,IndexError):pass
  peak=max(peak,rss)
  if rss>6*1024**3 or time.monotonic()-t>140:
   reason='rss' if rss>6*1024**3 else 'wall';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(0.05)
 rc=p.wait()
record={'command':cmd,'returncode':rc,'seconds':time.monotonic()-t,'cpu_limit':120,'wall_limit':140,'address_space_limit':12*1024**3,'sampled_peak_rss':peak,'cap_reason':reason,'cpus':2}
(D/'logs'/f'{tag}.json').write_text(json.dumps(record,indent=2));print(json.dumps(record));sys.exit(rc)
