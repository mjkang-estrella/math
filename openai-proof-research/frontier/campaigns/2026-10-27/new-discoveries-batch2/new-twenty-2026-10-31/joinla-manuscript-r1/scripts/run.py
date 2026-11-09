"""Sequential foreground resource wrapper. Invoke with python3 -I."""
import os, sys, subprocess, resource, time, json
from pathlib import Path
base=Path(__file__).resolve().parent.parent
os.environ.update(MALLOC_ARENA_MAX='2',TMPDIR=str(base/'tmp'),TEMP=str(base/'tmp'),TMP=str(base/'tmp'),PYTHONDONTWRITEBYTECODE='1')
cpus=sorted(os.sched_getaffinity(0))[:2]
def setup():
 os.sched_setaffinity(0,cpus)
 resource.setrlimit(resource.RLIMIT_CPU,(120,120))
 hard=resource.getrlimit(resource.RLIMIT_AS)[1]
 resource.setrlimit(resource.RLIMIT_AS,(min(6*1024**3,hard) if hard>0 else 6*1024**3,hard))
 resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic();peak=0;reason=None
p=subprocess.Popen(sys.argv[2:],preexec_fn=setup,start_new_session=True)
while p.poll() is None:
 rss=0
 for d in Path('/proc').iterdir():
  if not d.name.isdigit():continue
  try:
   if os.getpgid(int(d.name))==p.pid:
    for line in (d/'status').read_text().splitlines():
     if line.startswith('VmRSS:'):rss+=int(line.split()[1])*1024
  except (OSError,ProcessLookupError):pass
 peak=max(peak,rss)
 if rss>6*1024**3 or time.monotonic()-start>140:
  reason='RSS' if rss>6*1024**3 else 'wall';os.killpg(p.pid,9);break
 time.sleep(.1)
code=p.wait()
r={'command':sys.argv[2:],'exit_code':code,'wall_seconds':time.monotonic()-start,'sampled_peak_group_rss_bytes':peak,'sampling_seconds':.1,'cpu_limit_seconds':120,'wall_limit_seconds':140,'rss_limit_bytes':6*1024**3,'cpus':cpus,'kill_reason':reason,'MALLOC_ARENA_MAX':'2'}
(base/'receipts'/sys.argv[1]).write_text(json.dumps(r,indent=2)+'\n')
sys.exit(code if code>=0 else 1)
