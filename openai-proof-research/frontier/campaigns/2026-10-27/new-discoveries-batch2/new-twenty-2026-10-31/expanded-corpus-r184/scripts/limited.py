import os, resource, subprocess, time, sys, pathlib, json, signal
D=pathlib.Path(__file__).resolve().parents[1]
def pre():
 os.setsid(); os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
 resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
t=time.monotonic(); peak=0; reason=None
with (D/'logs'/f'{sys.argv[1]}.log').open('w') as log:
 p=subprocess.Popen(sys.argv[2:],stdout=log,stderr=subprocess.STDOUT,preexec_fn=pre,env={**os.environ,'MALLOC_ARENA_MAX':'2','OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'2','PYTHONDONTWRITEBYTECODE':'1','TMPDIR':str(D/'outputs')})
 while p.poll() is None:
  rss=0
  for x in pathlib.Path('/proc').iterdir():
   if not x.name.isdigit(): continue
   try:
    if os.getpgid(int(x.name))!=p.pid: continue
    rss+=int(next(l.split()[1] for l in (x/'status').read_text().splitlines() if l.startswith('VmRSS:')))*1024
   except (OSError,StopIteration,ValueError): pass
  peak=max(peak,rss)
  if rss>6*1024**3 or time.monotonic()-t>140:
   reason='process-group RSS or wall cap'; os.killpg(p.pid,signal.SIGKILL); break
  time.sleep(.1)
 p.wait()
r={'returncode':p.returncode,'wall_seconds':time.monotonic()-t,'sampled_group_rss_peak':peak,'cap_reason':reason,'limits':'2 CPUs, per-process CPU 120s, group sampled RSS 6 GiB, wall 140s, MALLOC_ARENA_MAX=2'}
(D/'logs'/f'{sys.argv[1]}.receipt.json').write_text(json.dumps(r,indent=2)+'\n'); print(json.dumps(r))
