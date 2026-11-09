import os,sys,time,subprocess,resource,json,signal,fcntl
from pathlib import Path
B=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/nanostar-manuscript-r1')
os.chdir(B)
for d in ['tmp','receipts','qa']: (B/d).mkdir(exist_ok=True)
lock=open(B/'tmp/process.lock','w');fcntl.flock(lock,fcntl.LOCK_EX)
env=dict(os.environ,MALLOC_ARENA_MAX='2',TMPDIR=str(B/'tmp'),TMP=str(B/'tmp'),TEMP=str(B/'tmp'),PYTHONDONTWRITEBYTECODE='1',XDG_CACHE_HOME=str(B/'tmp'))
def limits():
 os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
t=time.monotonic();p=subprocess.Popen(sys.argv[1:],env=env,preexec_fn=limits);peak=0;reason=None
while p.poll() is None:
 rss=0
 for q in Path('/proc').iterdir():
  if not q.name.isdigit(): continue
  try:
   st=(q/'stat').read_text().split(') ')[1].split()
   if int(st[2])==p.pid:
    rss+=int((q/'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
  except (OSError,ValueError,IndexError): pass
 peak=max(peak,rss)
 if rss>6*1024**3 or time.monotonic()-t>140:
  reason='RSS' if rss>6*1024**3 else 'wall';os.killpg(p.pid,signal.SIGKILL);break
 time.sleep(.05)
rc=p.wait();receipt={'command':sys.argv[1:],'exit_code':rc,'wall_seconds':time.monotonic()-t,'sampled_peak_RSS_bytes':peak,'kill_reason':reason,'CPU_limit_seconds':120,'wall_limit_seconds':140,'RSS_limit_bytes':6*1024**3,'CPU_affinity_count':2,'MALLOC_ARENA_MAX':'2','sampling_seconds':.05}
(B/'receipts'/('resource-'+str(time.time_ns())+'.json')).write_text(json.dumps(receipt,indent=2)+'\n');sys.exit(rc)
