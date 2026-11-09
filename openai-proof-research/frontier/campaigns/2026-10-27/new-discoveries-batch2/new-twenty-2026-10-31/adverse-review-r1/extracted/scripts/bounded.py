"""One bounded process group; private RSS sampled every 0.1 seconds."""
import os,sys,subprocess,time,resource,signal,json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
label=sys.argv[1];cmd=sys.argv[2:]
env=os.environ.copy();env.update(MALLOC_ARENA_MAX='2',TMPDIR=str(root/'tmp'),PYTHONDONTWRITEBYTECODE='1')
(root/'tmp').mkdir(exist_ok=True)
def limits():
 os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120))
t=time.monotonic();peak=0;reason=None
with (root/'logs'/f'{label}.log').open('w') as out:
 p=subprocess.Popen(cmd,stdout=out,stderr=subprocess.STDOUT,env=env,preexec_fn=limits)
 while p.poll() is None:
  rss=0
  # Include descendants even if a checker starts a worker.
  for proc in Path('/proc').glob('[0-9]*'):
   try:
    if os.getpgid(int(proc.name))!=p.pid:continue
    vals=(proc/'smaps_rollup').read_text().splitlines()
    rss+=sum(int(s.split()[1])*1024 for s in vals if s.startswith(('Private_Clean:','Private_Dirty:','Private_Hugetlb:')))
   except (OSError,ValueError,ProcessLookupError):pass
  peak=max(peak,rss)
  if rss>6*1024**3:reason='private RSS exceeded 6 GiB'
  if time.monotonic()-t>140:reason='wall exceeded 140 seconds'
  if reason:os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.1)
 rc=p.wait()
 # No lingering descendants.
 try:os.killpg(p.pid,signal.SIGKILL)
 except ProcessLookupError:pass
receipt={'command':cmd,'exit':rc,'seconds':time.monotonic()-t,'peak_sampled_private_rss_bytes':peak,'termination':reason,'cpu_limit_seconds':120,'wall_limit_seconds':140,'max_cpus':2,'sample_seconds':.1}
(root/'receipts'/f'{label}.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
with (root/'logs'/f'{label}.log').open('rb') as log:
 log.seek(0,2); size=log.tell(); log.seek(max(0,size-3000)); print(log.read().decode(errors='replace'))
sys.exit(rc if rc else bool(reason))
