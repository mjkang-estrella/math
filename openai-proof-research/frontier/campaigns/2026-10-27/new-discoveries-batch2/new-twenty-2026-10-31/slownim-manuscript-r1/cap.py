"""Foreground command runner: lane-local writes, two CPUs, sampled RSS and time caps."""
import os, sys, time, resource, subprocess, signal, json
from pathlib import Path
lane=Path(__file__).resolve().parent
os.chdir(lane)
for name in ('tmp','cache','logs'):(lane/name).mkdir(exist_ok=True)
os.environ.update(TMPDIR=str(lane/'tmp'),TMP=str(lane/'tmp'),TEMP=str(lane/'tmp'),XDG_CACHE_HOME=str(lane/'cache'),MPLCONFIGDIR=str(lane/'cache'),PYTHONDONTWRITEBYTECODE='1',MALLOC_ARENA_MAX='2')
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120))
 resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
start=time.monotonic(); peak=0; reason=None
p=subprocess.Popen(sys.argv[1:],start_new_session=True,preexec_fn=limits)
while p.poll() is None:
 rss=0
 for d in Path('/proc').iterdir():
  if not d.name.isdigit():continue
  try:
   stat=(d/'stat').read_text().split(') ',1)[1].split()
   if int(stat[2])==p.pid:rss+=int(stat[21])*os.sysconf('SC_PAGE_SIZE')
  except (OSError,ValueError,IndexError):pass
 peak=max(peak,rss)
 if rss>6*1024**3 or time.monotonic()-start>140:
  reason='RSS or wall cap';os.killpg(p.pid,signal.SIGKILL);break
 time.sleep(.1)
code=p.wait()
record=dict(command=sys.argv[1:],exit=code,seconds=time.monotonic()-start,sampled_peak_rss_bytes=peak,reason=reason,cpus=sorted(os.sched_getaffinity(0)))
with (lane/'logs/resource.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
sys.exit(code if code>=0 else 128-code)
