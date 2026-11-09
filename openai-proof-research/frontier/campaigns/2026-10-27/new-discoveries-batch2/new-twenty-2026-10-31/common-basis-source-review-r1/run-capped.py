from pathlib import Path
import subprocess,resource,os,time,json,sys
L=Path(__file__).resolve().parent
cmd=[sys.executable,'-I','-B',str(L/'check.py')]
def limits():
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
t=time.monotonic();peak=0;reason=None
with (L/'math-capped.log').open('w') as f:
 p=subprocess.Popen(cmd,stdout=f,stderr=subprocess.STDOUT,preexec_fn=limits,env=dict(os.environ,OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',MALLOC_ARENA_MAX='2'))
 while p.poll() is None:
  try:
   s=Path('/proc')/str(p.pid)/'status';rss=next(int(l.split()[1])*1024 for l in s.read_text().splitlines() if l.startswith('VmRSS:'));peak=max(peak,rss)
   if rss>6*1024**3:reason='rss';p.kill()
  except (FileNotFoundError,StopIteration):pass
  if time.monotonic()-t>140:reason='wall';p.kill()
  time.sleep(.01)
 rc=p.wait()
(L/'math-capped.receipt.json').write_text(json.dumps({'command':cmd,'exit':rc,'wall_seconds':time.monotonic()-t,'sampled_rss_bytes':peak,'cap_reason':reason,'limits':{'cpu_seconds':120,'wall_seconds':140,'rss_bytes':6*1024**3,'AS_bytes':12*1024**3,'cpus':2},'note':'10ms process RSS samples are not transient-peak guarantee; no child computation'},indent=2));assert rc==0
