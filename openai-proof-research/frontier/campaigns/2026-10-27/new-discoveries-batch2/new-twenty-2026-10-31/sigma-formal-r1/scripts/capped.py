#!/usr/bin/env python3
import os,resource,subprocess,sys,time,json,signal
from pathlib import Path
start=time.monotonic()
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
def limits():
 os.setsid()
 resource.setrlimit(resource.RLIMIT_CPU,(120,120))
 resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
env=dict(os.environ,MALLOC_ARENA_MAX='2',OMP_NUM_THREADS='2',OPENBLAS_NUM_THREADS='2')
proc=subprocess.Popen(sys.argv[1:],env=env,preexec_fn=limits)
peak=0; reason=None
while proc.poll() is None:
 try:
  rss=0
  for status in Path('/proc').glob('[0-9]*/status'):
   try:
    pid=int(status.parent.name)
    if os.getpgid(pid)==proc.pid:
     rss+=int(next(x for x in status.read_text().splitlines() if x.startswith('VmRSS:')).split()[1])*1024
   except (FileNotFoundError,StopIteration,ProcessLookupError,PermissionError): pass
  peak=max(peak,rss)
 except (FileNotFoundError,StopIteration,ProcessLookupError): pass
 if peak>6*1024**3 or time.monotonic()-start>140:
  reason='RSS' if peak>6*1024**3 else 'wall'; os.killpg(proc.pid,signal.SIGKILL); break
 time.sleep(.05)
code=proc.wait()
print(json.dumps(dict(command=sys.argv[1:],exit=code,peak_rss_bytes=peak,wall_seconds=time.monotonic()-start,kill_reason=reason)),file=sys.stderr)
sys.exit(code if code>=0 else 128-code)
