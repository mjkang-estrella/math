import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,json,time,hashlib,datetime,traceback,urllib.request,concurrent.futures,re
from pathlib import Path
L=Path(__file__).resolve().parent
START=time.monotonic(); READS=[]
def sha(b): return hashlib.sha256(b).hexdigest()
def write(n,b):
 p=(L/n).resolve(); assert p.is_relative_to(L); p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(b if isinstance(b,bytes) else b.encode())
def save(n,o): write(n,json.dumps(o,ensure_ascii=False,indent=2)+'\n')
def read(p):
 p=Path(p); assert 'crown' not in str(p).lower() and 'transitive-bunkbed-reach-bridge-formal-pi-r4' not in str(p)
 b=p.read_bytes(); READS.append({'path':str(p),'bytes':len(b),'sha256':sha(b)}); return b
exitcode=0
try:
 exec(compile(read(L/(sys.argv[1]+'.py')),sys.argv[1]+'.py','exec'))
except BaseException:
 exitcode=1; traceback.print_exc()
finally:
 u=resource.getrusage(resource.RUSAGE_SELF); c=resource.getrusage(resource.RUSAGE_CHILDREN)
 save('receipts/run-'+str(time.time_ns())+'.json',{'command':sys.argv,'exit_code':exitcode,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'affinity':sorted(os.sched_getaffinity(0)),'cpu_limit':120,'as_limit':6*1024**3,'external_wall_timeout':140,'wall':time.monotonic()-START,'self_cpu':u.ru_utime+u.ru_stime,'self_maxrss_KiB':u.ru_maxrss,'children_cpu':c.ru_utime+c.ru_stime,'reads':READS,'telemetry_limit':'Self high-water and reaped-child usage, not concurrent group peak; no child processes launched by runner.'})
sys.exit(exitcode)
