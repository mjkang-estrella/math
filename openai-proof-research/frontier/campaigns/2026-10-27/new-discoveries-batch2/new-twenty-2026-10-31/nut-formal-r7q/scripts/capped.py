import os,sys,time,subprocess,resource,json,signal
from pathlib import Path
log=Path(sys.argv[1]); cmd=sys.argv[2:]
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120))
 os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
env=dict(os.environ,MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1')
start=time.monotonic();peak=0;reason=None
with log.open('w') as f:
 p=subprocess.Popen(cmd,stdout=f,stderr=subprocess.STDOUT,env=env,preexec_fn=limits,start_new_session=True)
 while p.poll() is None:
  rss=0;cpu=0
  for entry in Path('/proc').iterdir():
   if not entry.name.isdigit():continue
   try:
    st=(entry/'stat').read_text().split(') ',1)[1].split()
    if int(st[2])!=p.pid:continue
    cpu+=(int(st[11])+int(st[12]))/os.sysconf('SC_CLK_TCK')
    lines=(entry/'smaps_rollup').read_text().splitlines()
    rss+=sum(int(x.split()[1]) for x in lines if x.startswith(('Private_Clean:','Private_Dirty:','Private_Hugetlb:')))*1024
   except (FileNotFoundError,ProcessLookupError,PermissionError):pass
  peak=max(peak,rss)
  if rss>5.75*1024**3:reason='private RSS cap'
  if cpu>120:reason='group CPU cap'
  if time.monotonic()-start>140:reason='wall cap'
  if reason:os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.05)
 rc=p.wait()
receipt={'command':cmd,'exit':rc,'wall_seconds':time.monotonic()-start,'peak_private_bytes':peak,'cap_reason':reason}
log.with_suffix(log.suffix+'.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt));sys.exit(rc if rc else (1 if reason else 0))
