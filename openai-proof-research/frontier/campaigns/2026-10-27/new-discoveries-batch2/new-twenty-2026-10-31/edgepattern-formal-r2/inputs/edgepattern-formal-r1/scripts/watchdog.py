#!/usr/bin/env python3
import os,sys,time,subprocess,resource,json,signal
from pathlib import Path

def main():
 log=Path(sys.argv[1]); cmd=sys.argv[2:]; start=time.monotonic(); peak=0; limit=6*1024**3; why=None
 def limits():
  os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); os.setsid()
 env=os.environ.copy();env['MALLOC_ARENA_MAX']='2';env['PYTHONDONTWRITEBYTECODE']='1'
 with log.open('w') as out:
  p=subprocess.Popen(cmd,stdout=out,stderr=subprocess.STDOUT,env=env,preexec_fn=limits)
  while p.poll() is None:
   rss=0
   try:
    # Smaps private RSS includes anonymous plus private file-backed resident pages.
    for line in Path('/proc/%s/smaps_rollup'%p.pid).read_text().splitlines():
     if line.startswith(('Private_Clean:','Private_Dirty:','Private_Hugetlb:')):rss+=int(line.split()[1])*1024
   except (OSError,ProcessLookupError):pass
   peak=max(peak,rss)
   if rss>limit or time.monotonic()-start>140:
    why='private RSS cap' if rss>limit else 'wall cap';os.killpg(p.pid,signal.SIGKILL);break
   time.sleep(.05)
  rc=p.wait()
 receipt=dict(command=cmd,exit_code=rc,elapsed_seconds=time.monotonic()-start,peak_sampled_private_rss_bytes=peak,killed=why,cpu_limit_seconds=120,wall_limit_seconds=140,rss_limit_bytes=limit)
 log.with_suffix(log.suffix+'.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));return rc if rc>=0 else 128-rc
if __name__=='__main__':sys.exit(main())
