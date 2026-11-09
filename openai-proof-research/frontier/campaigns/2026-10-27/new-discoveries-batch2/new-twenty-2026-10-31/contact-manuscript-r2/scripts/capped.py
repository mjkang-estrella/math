import os,sys,resource,subprocess,time,signal,json
from pathlib import Path
lane=Path(__file__).resolve().parent.parent
log=lane/sys.argv[1]
def limits():
 os.setsid(); os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
env=os.environ.copy();env.update(TMPDIR=str(lane/'tmp'),TMP=str(lane/'tmp'),TEMP=str(lane/'tmp'),XDG_CACHE_HOME=str(lane/'cache'),PYTHONPYCACHEPREFIX=str(lane/'cache'),MALLOC_ARENA_MAX='2')
start=time.monotonic();peak=0;killed=None
with log.open('w') as out:
 p=subprocess.Popen(sys.argv[2:],stdout=out,stderr=subprocess.STDOUT,env=env,preexec_fn=limits)
 while p.poll() is None:
  rss=0;cpu=0
  for q in Path('/proc').iterdir():
   if not q.name.isdigit():continue
   try:
    f=(q/'stat').read_text().rsplit(')',1)[1].split()
    if int(f[2])!=p.pid:continue
    cpu+=(int(f[11])+int(f[12]))/os.sysconf('SC_CLK_TCK')
    for l in (q/'status').read_text().splitlines():
     if l.startswith('VmRSS:'):rss+=int(l.split()[1])*1024
   except (OSError,ValueError):pass
  peak=max(peak,rss)
  if rss>6*1024**3 or cpu>120 or time.monotonic()-start>140:
   killed='resource cap';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.05)
 rc=p.wait()
r={'command':sys.argv[2:],'returncode':rc,'wall_seconds':time.monotonic()-start,'peak_total_group_rss_bytes':peak,'killed':killed,'cpu_limit_seconds':120,'wall_limit_seconds':140,'cpus':2,'address_space_limit_bytes':6*1024**3,'MALLOC_ARENA_MAX':2}
log.with_suffix(log.suffix+'.receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));sys.exit(rc)
