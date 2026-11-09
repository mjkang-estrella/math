import os,sys,subprocess,resource,time,pathlib,signal,json
D=pathlib.Path(__file__).resolve().parents[1]; name=sys.argv[1]
def pre():
 os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
t=time.monotonic();peak=0;why=None
with (D/f'logs/{name}.log').open('x') as f:
 p=subprocess.Popen(sys.argv[2:],stdout=f,stderr=subprocess.STDOUT,preexec_fn=pre,env={**os.environ,'MALLOC_ARENA_MAX':'2','TMPDIR':str(D/'tmp'),'PYTHONDONTWRITEBYTECODE':'1','OMP_NUM_THREADS':'2','OPENBLAS_NUM_THREADS':'1'})
 while p.poll() is None:
  rss=0
  for q in pathlib.Path('/proc').glob('[0-9]*'):
   try:
    st=(q/'stat').read_text().split(') ')[1].split()
    if int(st[2])==p.pid:rss+=int(st[21])*os.sysconf('SC_PAGE_SIZE')
   except (OSError,ValueError,IndexError):pass
  peak=max(peak,rss)
  if rss>6*1024**3 or time.monotonic()-t>140:why='RSS/wall cap';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.1)
 p.wait()
r={'returncode':p.returncode,'wall':time.monotonic()-t,'sampled_group_peak':peak,'cap_reason':why};(D/f'logs/{name}.json').write_text(json.dumps(r,indent=2));print(r)
