import os,sys,subprocess,resource,time,json,signal
from pathlib import Path
O=Path(__file__).resolve().parent; label=sys.argv[1]; cmd=sys.argv[2:]; cpus=sorted(os.sched_getaffinity(0))[:2]
def setup():
 os.setsid(); os.sched_setaffinity(0,cpus); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
t=time.monotonic(); peak=0; reason=None
with (O/(label+'.log')).open('w') as f:
 p=subprocess.Popen(cmd,stdout=f,stderr=subprocess.STDOUT,preexec_fn=setup)
 while p.poll() is None:
  rss=0
  for q in Path('/proc').glob('[0-9]*'):
   try:
    fields=(q/'stat').read_text().split();
    if int(fields[4])==p.pid: rss+=int(fields[23])*os.sysconf('SC_PAGE_SIZE')
   except (OSError,ValueError,IndexError): pass
  peak=max(peak,rss)
  if rss>6*1024**3 or time.monotonic()-t>140:
   reason='RSS' if rss>6*1024**3 else 'wall'; os.killpg(p.pid,signal.SIGKILL); break
  time.sleep(.1)
 p.wait()
r={'cmd':cmd,'cpus':cpus,'cpu_limit_s':120,'wall_limit_s':140,'AS_GiB':12,'RSS_GiB':6,'sampled_peak_rss':peak,'sampling_s':.1,'exit':p.returncode,'reason':reason,'wall_s':time.monotonic()-t}; (O/(label+'.guard.json')).write_text(json.dumps(r,indent=2)+'\n'); print(r)
