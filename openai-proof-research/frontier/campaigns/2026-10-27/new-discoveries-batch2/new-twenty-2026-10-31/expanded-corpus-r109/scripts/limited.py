import os,resource,subprocess,time,sys,pathlib,json,signal
D=pathlib.Path(__file__).resolve().parents[1]
name=sys.argv[1]
def pre():
 os.setsid(); os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
t=time.monotonic(); peak=0; reason=None
with (D/f'logs/{name}.log').open('w') as log:
 p=subprocess.Popen(sys.argv[2:],stdout=log,stderr=subprocess.STDOUT,preexec_fn=pre,env={**os.environ,'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'2'})
 while p.poll() is None:
  try:
   rss=0
   for entry in pathlib.Path('/proc').iterdir():
    if not entry.name.isdigit():continue
    try:
     if os.getpgid(int(entry.name))!=p.pid:continue
     rss+=int(next(l.split()[1] for l in (entry/'status').read_text().splitlines() if l.startswith('VmRSS:')))*1024
    except (OSError,StopIteration,ProcessLookupError):pass
   peak=max(peak,rss)
  except OSError:pass
  if peak>6*1024**3 or time.monotonic()-t>140:
   reason='RSS or wall cap';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.05)
 p.wait()
r={'returncode':p.returncode,'wall_seconds':time.monotonic()-t,'sampled_process_group_rss_peak_bytes':peak,'cap_reason':reason,'limits':'2 CPUs; CPU 120s; wall 140s; sampled process-group RSS 6 GiB; AS 64 GiB; monitoring is not cgroup/transient guarantee'}
(D/f'logs/{name}.receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
