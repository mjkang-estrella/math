from pathlib import Path
import subprocess,os,resource,time,json,hashlib
p=Path(__file__).parent.resolve(); pk=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages');lean='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
os.environ['LEAN_PATH']=':'.join([str(p)]+[str(f/'.lake/build/lib/lean') for f in pk.iterdir()]);os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]));resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120));s=time.time()
log=p/('lean-'+str(time.time_ns())+'.log')
with log.open('w') as out:
 proc=subprocess.Popen([lean,'-j1','-DwarningAsError=true','-o',str(p/'Game.olean'),str(p/'Game.lean')],stdout=out,stderr=subprocess.STDOUT,cwd=p)
 peak=0;reason=None
 while proc.poll() is None:
  try:
   status=Path('/proc')/str(proc.pid)/'status'
   vals=[x for x in status.read_text().splitlines() if x.startswith('VmRSS:')]
   if vals: peak=max(peak,int(vals[0].split()[1])*1024)
  except FileNotFoundError:pass
  if peak>6*1024**3 or time.time()-s>140:
   reason='RSS or wall cap';proc.kill();break
  time.sleep(.05)
 rc=proc.wait()
(p/'lean.log').write_text(log.read_text());print(log.read_text()[-3000:]);rec={'exit':rc,'wall_s':time.time()-s,'peak_sampled_RSS_bytes':peak,'RSS_limit_bytes':6*1024**3,'AS_limit_bytes':12*1024**3,'cpu_s_limit':120,'wall_limit_s':140,'cpus':sorted(os.sched_getaffinity(0)),'log':log.name,'reason':reason,'source_sha256':hashlib.sha256((p/'Game.lean').read_bytes()).hexdigest()};(p/'lean-receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec)
