import os,sys,subprocess,time,resource,json
from pathlib import Path
os.environ['MALLOC_ARENA_MAX']='2'
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120))
 resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
t=time.monotonic(); peak=0
with open(sys.argv[1],'w') as log:
 p=subprocess.Popen(sys.argv[2:],stdout=log,stderr=subprocess.STDOUT,preexec_fn=limits,start_new_session=True)
 while p.poll() is None:
  private=0
  for proc in Path('/proc').iterdir():
   if not proc.name.isdigit(): continue
   try:
    if os.getpgid(int(proc.name)) != p.pid: continue
    for line in (proc/'smaps_rollup').read_text().splitlines():
     if line.startswith(('Private_Clean:','Private_Dirty:','Private_Hugetlb:')): private+=int(line.split()[1])*1024
   except (FileNotFoundError,ProcessLookupError,PermissionError): pass
  peak=max(peak,private)
  if private>6*1024**3 or time.monotonic()-t>140:
   import signal
   os.killpg(p.pid,signal.SIGKILL); p.wait(); break
  time.sleep(.1)
receipt={'command':sys.argv[2:],'exit':p.returncode,'wall_seconds':time.monotonic()-t,'sampled_private_rss_bytes':peak}
Path(sys.argv[1]+'.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt));sys.exit(p.returncode if p.returncode>=0 else 1)
