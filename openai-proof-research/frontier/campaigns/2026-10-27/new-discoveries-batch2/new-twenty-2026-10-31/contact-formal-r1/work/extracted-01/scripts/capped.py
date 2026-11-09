#!/usr/bin/env python3
import os,sys,subprocess,time,resource,json,signal
from pathlib import Path
log=Path(sys.argv[1]); cmd=sys.argv[2:]
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120))
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
 os.setsid()
env=os.environ.copy();env['MALLOC_ARENA_MAX']='2';env['TMPDIR']=str(log.parent.resolve())
start=time.monotonic();peak=0;samples=[];killed=None
with log.open('w') as out:
 p=subprocess.Popen(cmd,stdout=out,stderr=subprocess.STDOUT,env=env,preexec_fn=limits)
 while p.poll() is None:
  rss=0
  try:
   for line in Path(f'/proc/{p.pid}/smaps_rollup').read_text().splitlines():
    if line.startswith(('Private_Clean:','Private_Dirty:','Private_Hugetlb:')):rss+=int(line.split()[1])*1024
  except (FileNotFoundError,ProcessLookupError):pass
  peak=max(peak,rss);samples.append([round(time.monotonic()-start,3),rss])
  if rss>6*1024**3 or time.monotonic()-start>140:
   killed='private RSS' if rss>6*1024**3 else 'wall';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.2)
 rc=p.wait()
log.with_suffix(log.suffix+'.receipt.json').write_text(json.dumps(dict(command=cmd,returncode=rc,wall=time.monotonic()-start,peak_private_bytes=peak,killed=killed,samples=samples),indent=2)+'\n')

if log.stat().st_size > 1024*1024:
 import gzip
 with log.open('rb') as src, gzip.open(str(log)+'.gz','wb') as dst:
  import shutil
  shutil.copyfileobj(src,dst)
 log.write_text('Full output archived losslessly at '+log.name+'.gz\n')
print(str(log)+': returncode '+str(rc));sys.exit(rc)
