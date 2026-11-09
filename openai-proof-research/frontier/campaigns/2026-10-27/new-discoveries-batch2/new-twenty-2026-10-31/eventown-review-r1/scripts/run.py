import os,sys,subprocess,resource,time,json,pathlib,signal
root=pathlib.Path(__file__).resolve().parents[1]; os.chdir(root)
name=sys.argv[1]; command=sys.argv[2:]; start=time.monotonic()
command=['systemd-run','--user','--scope','--quiet','-p','MemoryMax=6G','-p','CPUQuota=200%','--']+command
def limit():
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));os.setsid()
env=dict(os.environ,MALLOC_ARENA_MAX='2',TMPDIR=str(root/'replay'),PYTHONDONTWRITEBYTECODE='1')
peak=0; reason=None
with (root/'logs'/f'{name}.log').open('w') as log:
 p=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,env=env,preexec_fn=limit)
 while p.poll() is None:
  try:
   rss=0
   for proc in pathlib.Path('/proc').iterdir():
    if not proc.name.isdigit():continue
    try:
     if int((proc/'stat').read_text().split(') ',1)[1].split()[2]) != p.pid:continue
     rss+=sum(int(l.split()[1])*1024 for l in (proc/'smaps_rollup').read_text().splitlines() if l.startswith(('Private_Clean:','Private_Dirty:','Private_Hugetlb:')))
    except (OSError,ValueError,IndexError):pass
   peak=max(peak,rss)
  except (OSError,ValueError):pass
  if peak>6*1024**3 or time.monotonic()-start>140:
   reason='private RSS cap' if peak>6*1024**3 else 'wall cap';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.1)
 rc=p.wait()
# eliminate any descendants even after normal termination
try:os.killpg(p.pid,signal.SIGKILL)
except ProcessLookupError:pass
r={'command':command,'returncode':rc,'wall_seconds':time.monotonic()-start,'peak_sampled_private_bytes':peak,'termination':reason,'cpu_seconds_limit':120,'affinity_cpus':2,'systemd_scope':'systemd-run --user --scope MemoryMax=6G CPUQuota=200%; affinity, inherited CPU rlimit, group private RSS sampling, wall cap'}
(root/'logs'/f'{name}.json').write_text(json.dumps(r,indent=2)); print(json.dumps(r))
