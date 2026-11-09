from pathlib import Path
import subprocess,os,resource,sys,time,json,signal
L=Path(__file__).resolve().parent;name=sys.argv[1];cmd=sys.argv[2:]
def caps():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
env=dict(os.environ,MALLOC_ARENA_MAX='2',OMP_NUM_THREADS='2',OPENBLAS_NUM_THREADS='2',TMPDIR=str(L));t=time.monotonic();peak=0;ns=0;stopped=None
with (L/(name+'.log')).open('xb') as f:
 p=subprocess.Popen(cmd,stdout=f,stderr=subprocess.STDOUT,env=env,preexec_fn=caps,start_new_session=True)
 while p.poll() is None:
  rss=0
  for q in Path('/proc').glob('[0-9]*'):
   try:
    fields=(q/'stat').read_text().split()
    if int(fields[4])==p.pid:
     rss+=int(next(z.split()[1] for z in (q/'status').read_text().splitlines() if z.startswith('VmRSS:')))*1024
   except (OSError,ValueError,StopIteration):pass
  peak=max(peak,rss);ns+=1
  if rss>=6*1024**3 or time.monotonic()-t>140:
   stopped='rss' if rss>=6*1024**3 else 'wall';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.1)
 code=p.wait()
(L/(name+'.run.json')).write_text(json.dumps({'command':cmd,'exit':code,'wall_seconds':time.monotonic()-t,'cpu_seconds_limit':120,'address_space_gib':6,'cpus':2,'sampled_peak_group_rss_bytes':peak,'rss_samples':ns,'stopped':stopped},indent=2));print(name,code)
