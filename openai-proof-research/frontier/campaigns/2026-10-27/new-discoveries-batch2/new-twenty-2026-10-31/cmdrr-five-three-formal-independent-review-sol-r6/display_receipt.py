import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(10,10))
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912))
from pathlib import Path
import sys,json,re,hashlib,time
lane=Path(__file__).resolve().parent
os.chdir(lane)
rec={'time_ns':time.time_ns(),'argv':sys.argv,'scope':'Standalone receipt-driven own-log display; self caps only, no compiler-runner/group/native-UI telemetry','affinity':sorted(os.sched_getaffinity(0)),'cpu_s':10,'AS_bytes':536870912,'outer_timeout_s':20}
data=b''
try:
 name=sys.argv[1]
 assert re.fullmatch(r'[0-9]+_[A-Za-z0-9_.-]+[.]json',name), 'Pass exact receipt basename from RECEIPT= output, not a log path or a guess'
 rp=(lane/'receipt'/name).resolve();assert rp.parent==lane/'receipt'
 assert rp.stat().st_size<=1048576
 rb=rp.read_bytes();r=json.loads(rb)
 p=Path(r['log']).resolve();assert p.parent==lane/'logs'
 assert r['exit'] is not None and r['group_members_left']==[]
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(65536),b''):h.update(b)
 assert h.hexdigest()==r['log_sha256'], 'Receipt/log hash mismatch'
 offset=int(sys.argv[2]) if len(sys.argv)>2 else 0
 length=int(sys.argv[3]) if len(sys.argv)>3 else 12000
 assert offset>=0 and 0<length<=16384
 with p.open('rb') as f:f.seek(offset);data=f.read(length)
 rec.update(receipt=name,receipt_sha256=hashlib.sha256(rb).hexdigest(),log=str(p),log_sha256=h.hexdigest(),runner_exit=r['exit'],offset=offset,bytes=len(data),exit=0)
except Exception as e:
 rec.update(exit=1,error=type(e).__name__+': '+str(e))
out=lane/'audit/displays'/('receipt-display-'+str(rec['time_ns'])+'.json')
out.write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps(rec),flush=True)
if rec['exit']==0:
 sys.stdout.buffer.write(data);sys.stdout.buffer.write(b'\n');sys.stdout.buffer.flush()
sys.exit(rec['exit'])
