import sys
sys.dont_write_bytecode=True
import os,sys,time,resource,subprocess,json,pathlib
root=pathlib.Path(__file__).resolve().parents[1]; os.chdir(root)
os.environ.update(MALLOC_ARENA_MAX='2',TMPDIR=str(root/'tmp'),PYTHONDONTWRITEBYTECODE='1',HOME=str(root/'tmp'),XDG_CACHE_HOME=str(root/'tmp'))
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CORE,(0,0)); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
label=sys.argv[1]; start=time.monotonic(); peak=0
command=sys.argv[2:]
if 'python' in pathlib.Path(command[0]).name and '-B' not in command: command.insert(1,'-B')
p=subprocess.Popen(command,start_new_session=True)
while p.poll() is None:
 try:
  rss=int(next(x.split()[1] for x in pathlib.Path('/proc/%d/status'%p.pid).read_text().splitlines() if x.startswith('VmRSS:')))*1024
  peak=max(peak,rss)
 except (OSError,StopIteration): pass
 if time.monotonic()-start>135 or peak>6*1024**3:
  import signal
  os.killpg(p.pid,signal.SIGKILL); p.wait(); break
 time.sleep(.05)
r={'command':command,'exit':p.returncode,'wall_seconds':time.monotonic()-start,'sampled_peak_rss_bytes':peak,'cpus':sorted(os.sched_getaffinity(0)),'cpu_limit_seconds':120,'wall_kill_seconds':135,'rss_limit_bytes':6*1024**3,'MALLOC_ARENA_MAX':'2'}
(root/'receipts'/('cap-'+label+'.json')).write_text(json.dumps(r,indent=2)+'\n')
sys.exit(p.returncode)
