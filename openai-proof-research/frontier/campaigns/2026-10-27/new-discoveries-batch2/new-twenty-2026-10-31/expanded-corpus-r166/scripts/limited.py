import os,resource,subprocess,time,sys,pathlib,json,signal
D=pathlib.Path(__file__).resolve().parents[1]
name=sys.argv[1]
def pre():
 os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
t=time.monotonic();peak=0;reason=None
with (D/f'logs/{name}.log').open('w') as log:
 p=subprocess.Popen(sys.argv[2:],stdout=log,stderr=subprocess.STDOUT,preexec_fn=pre,env={**os.environ,'MALLOC_ARENA_MAX':'2','OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'2','PYTHONDONTWRITEBYTECODE':'1','TMPDIR':str(D/'outputs')})
 while p.poll() is None:
  total=0
  for stat in pathlib.Path('/proc').glob('[0-9]*/stat'):
   try:
    s=stat.read_text().rsplit(')',1)[1].split()
    if int(s[2])==p.pid: total+=int(s[21])*os.sysconf('SC_PAGE_SIZE')
   except (OSError,ValueError,IndexError):pass
  peak=max(peak,total)
  if total>6*1024**3 or time.monotonic()-t>140:
   reason='process-group RSS or wall cap';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.15)
 p.wait()
r={'returncode':p.returncode,'wall_seconds':time.monotonic()-t,'sampled_process_group_rss_peak_bytes':peak,'cap_reason':reason,'limits':'2 CPUs; CPU 120s per process; wall 140s; sampled process-group RSS 6 GiB; AS 12 GiB; not cgroup/transient guarantee'}
(D/f'logs/{name}.receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
