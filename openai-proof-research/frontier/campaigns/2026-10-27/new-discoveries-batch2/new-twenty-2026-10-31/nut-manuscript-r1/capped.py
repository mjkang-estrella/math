#!/usr/bin/env python3
import os,sys,time,subprocess,resource,json,signal
from pathlib import Path
receipt=Path(sys.argv[1]);cmd=sys.argv[2:]
def limits():
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));os.setsid()
env=dict(os.environ,MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1',TMPDIR=str(Path('tmp').resolve()))
Path('tmp').mkdir(exist_ok=True);start=time.monotonic();peak=0;reason=None
p=subprocess.Popen(cmd,env=env,preexec_fn=limits)
while p.poll() is None:
 rss=0
 for f in Path('/proc').glob('[0-9]*/stat'):
  try:
   parts=f.read_text().split();pid=int(parts[0]);pg=int(parts[4])
   if pg==p.pid:
    rss+=int((f.parent/'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
  except (OSError,ValueError,IndexError):pass
 peak=max(peak,rss)
 if rss>6*1024**3:reason='RSS limit'
 if time.monotonic()-start>140:reason='wall limit'
 if reason:os.killpg(p.pid,signal.SIGKILL);break
 time.sleep(.1)
rc=p.wait();receipt.parent.mkdir(parents=True,exist_ok=True)
receipt.write_text(json.dumps(dict(command=cmd,returncode=rc,wall_seconds=time.monotonic()-start,sampled_peak_rss_bytes=peak,cap_reason=reason,cpu_slots=2,cpu_seconds_limit=120,wall_seconds_limit=140,rss_bytes_limit=6*1024**3,MALLOC_ARENA_MAX='2'),indent=2)+'\n')
sys.exit(rc if rc>=0 else 1)
