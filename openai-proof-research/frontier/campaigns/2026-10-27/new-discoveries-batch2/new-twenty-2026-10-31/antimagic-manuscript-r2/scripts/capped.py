import os, sys, subprocess, resource, time, signal, pathlib, json
O=pathlib.Path(__file__).resolve().parents[1]
os.environ['MALLOC_ARENA_MAX']='2'
os.environ['PYTHONDONTWRITEBYTECODE']='1'
os.environ['TMPDIR']=str(O/'tmp');(O/'tmp').mkdir(exist_ok=True)
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120))
 resource.setrlimit(resource.RLIMIT_AS,(5*1024**3,5*1024**3))
start=time.monotonic();p=subprocess.Popen(sys.argv[1:],cwd=O,preexec_fn=limits,start_new_session=True)
peak=0;reason=None
while p.poll() is None:
 rss=0
 for f in pathlib.Path('/proc').glob('[0-9]*/stat'):
  try:
   s=f.read_text();v=s[s.rfind(')')+2:].split()
   if int(v[2])==p.pid:rss+=int(v[21])*os.sysconf('SC_PAGE_SIZE')
  except (FileNotFoundError,ProcessLookupError,PermissionError,ValueError):pass
 peak=max(peak,rss)
 if rss>=6*1024**3 or time.monotonic()-start>=139:
  reason='RSS or wall limit';os.killpg(p.pid,signal.SIGKILL);break
 time.sleep(.05)
code=p.wait()
r={'command':sys.argv[1:],'exit_code':code,'wall_seconds':time.monotonic()-start,'sampled_group_peak_RSS_bytes':peak,'cpu_limit_seconds':120,'wall_limit_seconds':140,'address_space_limit_bytes':5*1024**3,'cpu_affinity':sorted(os.sched_getaffinity(0)),'MALLOC_ARENA_MAX':'2','failure':reason}
(O/os.environ.get('PROCESS_RECEIPT_DIR','receipts')/('process-'+str(time.time_ns())+'.json')).write_text(json.dumps(r,indent=2)+'\n')
sys.exit(code if code>=0 else 1)
