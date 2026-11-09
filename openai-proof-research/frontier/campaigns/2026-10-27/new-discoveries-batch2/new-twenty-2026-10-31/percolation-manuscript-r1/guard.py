from pathlib import Path
import os,sys,subprocess,time,json,resource
D=Path(sys.argv[1]).resolve();label=sys.argv[2];cmd=sys.argv[3:]
os.environ.update(MALLOC_ARENA_MAX='2',TMPDIR=str(D/'tmp'),PYTHONDONTWRITEBYTECODE='1',XDG_CACHE_HOME=str(D/'tmp/cache'))
(D/'tmp').mkdir(exist_ok=True)
allowed=sorted(os.sched_getaffinity(0));os.sched_setaffinity(0,set(allowed[:2]))
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
start=time.monotonic();p=subprocess.Popen(cmd,cwd=D,preexec_fn=limits);peak=0;samples=0;reason=None
while p.poll() is None:
 try:
  text=Path(f'/proc/{p.pid}/status').read_text();rss=int(next(x for x in text.splitlines() if x.startswith('VmRSS:')).split()[1]);peak=max(peak,rss);samples+=1
 except (FileNotFoundError,StopIteration):pass
 if peak>6*1024**2 or time.monotonic()-start>140:
  reason='cap';p.kill();break
 time.sleep(.03)
rc=p.wait();out=dict(command=cmd,exit=rc,wall_seconds=time.monotonic()-start,sampled_peak_rss_kib=peak,samples=samples,cpu_affinity=allowed[:2],cpu_limit_seconds=120,wall_limit_seconds=140,rss_limit_gib=6,MALLOC_ARENA_MAX=2,cap_failure=reason)
(D/'receipts').mkdir(exist_ok=True);(D/'receipts'/f'{label}.json').write_text(json.dumps(out,indent=2)+'\n');sys.exit(rc)
