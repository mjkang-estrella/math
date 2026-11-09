import os, resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU, (10, 10))
resource.setrlimit(resource.RLIMIT_AS, (512*1024**2, 512*1024**2))
from pathlib import Path
import json, sys, time
lane=Path(__file__).resolve().parent
receipt=lane/'bootstrap-receipt.json'
assert not receipt.exists(), 'Do not overwrite the first bootstrap receipt'
start=time.monotonic(); reads=[]
for d in reversed([lane,*lane.parents]):
 f=d/'AGENTS.md'
 if f.is_file():
  text=f.read_text(); reads.append({'path':str(f),'characters':len(text)}); print('FILE',f,flush=True); print(text,flush=True)
f=lane/'TASK.txt'; text=f.read_text(); reads.append({'path':str(f),'characters':len(text)}); print('FILE',f,flush=True);print(text,flush=True)
u=resource.getrusage(resource.RUSAGE_SELF)
receipt.write_text(json.dumps({'argv':sys.argv,'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit_s':10,'AS_limit_bytes':512*1024**2,'external_wall_timeout_s':20,'reads':reads,'wall_seconds':time.monotonic()-start,'self_user_system_CPU_s':u.ru_utime+u.ru_stime,'self_peak_RSS_KiB':u.ru_maxrss,'limits':'Self high-water RSS, not group sampled telemetry/cgroup; external timeout wrapper not CPU-affinity attested'},indent=2)+'\n')
