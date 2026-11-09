import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(10,10))
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
from pathlib import Path
import sys,json,time,hashlib
lane=Path(__file__).resolve().parent
name=sys.argv[1];assert Path(name).name==name and name.endswith('.log')
q=(lane/'logs'/name).resolve();assert q.parent==lane/'logs' and q.is_file()
offset=int(sys.argv[2]);length=min(int(sys.argv[3]) if len(sys.argv)>3 else 12000,16384)
assert offset>=0 and 0<length<=16384
with q.open('rb') as f:f.seek(offset);b=f.read(length)
record={'utc':time.time(),'log':name,'offset':offset,'length':len(b),'chunk_sha256':hashlib.sha256(b).hexdigest(),'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit_s':10,'AS_limit_bytes':512*1024**2,'outer_timeout_s':20,'scope':'Prospective own-log display exception, self caps only; no sampled group/native display telemetry'}
with (lane/'DISPLAY-CALLS.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
print(json.dumps(record),flush=True)
sys.stdout.buffer.write(b);sys.stdout.buffer.write(b'\n');sys.stdout.buffer.flush()
