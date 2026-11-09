# Resource wrapper (adapted from expanded-corpus-r59/scripts/limited.py, copied into this lane).
# Claude-lane caps: 1 CPU affinity pair, CPU 120 s, wall 140 s, sampled RSS kill at 1.5 GiB, AS 4 GiB, MALLOC_ARENA_MAX=2.
import os,resource,subprocess,time,sys,pathlib,json,signal
D=pathlib.Path(__file__).resolve().parents[1]
name=sys.argv[1]
def pre():
 os.setsid(); os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,4*1024**3))
t=time.monotonic(); peak=0; reason=None
with (D/f'logs/{name}.log').open('w') as log:
 p=subprocess.Popen(sys.argv[2:],stdout=log,stderr=subprocess.STDOUT,preexec_fn=pre,cwd=str(D),env={**os.environ,'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','MALLOC_ARENA_MAX':'2','PYTHONDONTWRITEBYTECODE':'1'})
 while p.poll() is None:
  try:
   rss=int(next(l.split()[1] for l in pathlib.Path(f'/proc/{p.pid}/status').read_text().splitlines() if l.startswith('VmRSS:')))*1024;peak=max(peak,rss)
  except (OSError,StopIteration):pass
  if peak>1536*1024**2 or time.monotonic()-t>140:
   reason='RSS or wall cap';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.05)
 p.wait()
r={'cmd':sys.argv[2:],'returncode':p.returncode,'wall_seconds':round(time.monotonic()-t,3),'sampled_process_rss_peak_bytes':peak,'cap_reason':reason,'limits':'2 CPUs affinity; CPU 120s; wall 140s; sampled RSS kill 1.5 GiB; AS 4 GiB; MALLOC_ARENA_MAX=2'}
(D/f'logs/{name}.receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
