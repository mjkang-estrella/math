import os,sys,time,resource,subprocess,json,signal
from pathlib import Path
log=Path(sys.argv[1]);cmd=sys.argv[2:]
def limits():
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
 resource.setrlimit(resource.RLIMIT_CPU,(120,120))
 resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
 os.setsid()
env=dict(os.environ,MALLOC_ARENA_MAX='2',TMPDIR=str(Path.cwd()/'tmp'))
Path(env['TMPDIR']).mkdir(exist_ok=True)
start=time.monotonic(); peak=0;reason=None
with log.open('w') as f:
 p=subprocess.Popen(cmd,stdout=f,stderr=subprocess.STDOUT,env=env,preexec_fn=limits)
 while p.poll() is None:
  rss=0
  for proc in Path('/proc').iterdir():
   if not proc.name.isdigit():continue
   try:
    stat=(proc/'stat').read_text().split()
    if int(stat[5])!=p.pid:continue
    for line in (proc/'smaps_rollup').read_text().splitlines():
     if line.startswith(('Private_Clean:','Private_Dirty:','Private_Hugetlb:')):rss+=int(line.split()[1])*1024
   except (OSError,ValueError):pass
  peak=max(peak,rss)
  if rss>6*1024**3:reason='private RSS cap'
  if time.monotonic()-start>140:reason='wall cap'
  if reason:os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.1)
 rc=p.wait()
rec={'cmd':cmd,'exit_code':rc,'wall_seconds':time.monotonic()-start,'peak_sampled_private_rss_bytes':peak,'killed_reason':reason,'cpu_limit':120,'wall_limit':140,'cpus':2,'address_space_gib':64,'rss_limit_gib':6}
log.with_suffix(log.suffix+'.receipt.json').write_text(json.dumps(rec,indent=2))
print(json.dumps(rec))
sys.exit(rc if rc>=0 else 1)
