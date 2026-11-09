from pathlib import Path
import subprocess,sys,os,time,json,resource,signal
L=Path(__file__).resolve().parents[1]
tag=sys.argv[1];cmd=sys.argv[2:]
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
env=os.environ.copy();env.update(MALLOC_ARENA_MAX='2',TMPDIR=str(L/'tmp'),PYTHONDONTWRITEBYTECODE='1',XDG_CACHE_HOME=str(L/'tmp/cache'))
peak=0;start=time.monotonic()
with (L/f'logs/{tag}.log').open('w') as log:
 p=subprocess.Popen(cmd,cwd=L,env=env,stdout=log,stderr=subprocess.STDOUT)
 while p.poll() is None:
  try:
   for line in Path(f'/proc/{p.pid}/status').read_text().splitlines():
    if line.startswith('VmRSS:'): peak=max(peak,int(line.split()[1])*1024)
  except FileNotFoundError: pass
  if time.monotonic()-start>140 or peak>6*1024**3:p.kill();p.wait();raise RuntimeError('cap exceeded')
  time.sleep(.05)
r={'command':cmd,'exit_code':p.returncode,'seconds':time.monotonic()-start,'sampled_peak_rss_bytes':peak,'cpus':sorted(os.sched_getaffinity(0)),'cpu_limit_seconds':120,'wall_limit_seconds':140,'address_limit_bytes':6*1024**3,'MALLOC_ARENA_MAX':'2'}
(L/f'logs/{tag}.json').write_text(json.dumps(r,indent=2)+'\n');print(r);sys.exit(p.returncode)
