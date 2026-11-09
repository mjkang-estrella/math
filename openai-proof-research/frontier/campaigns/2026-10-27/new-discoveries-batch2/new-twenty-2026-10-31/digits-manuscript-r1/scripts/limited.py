from pathlib import Path
import os,sys,subprocess,resource,time,signal,json
W=Path(__file__).resolve().parents[1]
env=os.environ.copy();env.update(MALLOC_ARENA_MAX="2",TMPDIR=str(W/"tmp"),PYTHONDONTWRITEBYTECODE="1")
def limits():
 os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120))
def run(label,cmd,expected=0):
 start=time.monotonic();peak=0;killed=None
 with (W/'logs'/f'{label}.log').open('w') as f:
  p=subprocess.Popen(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
  while p.poll() is None:
   # Sum resident memory of the process group, counting shared pages conservatively.
   rss=0
   for proc in Path('/proc').iterdir():
    if not proc.name.isdigit():continue
    try:
     if os.getpgid(int(proc.name)) != p.pid:continue
     for line in (proc/'status').read_text().splitlines():
      if line.startswith('VmRSS:'):rss+=int(line.split()[1])
    except (OSError,ValueError,ProcessLookupError):pass
   peak=max(peak,rss)
   if rss>6*1024*1024 or time.monotonic()-start>140:
    killed='RSS or wall cap';os.killpg(p.pid,signal.SIGKILL);break
   time.sleep(.1)
  p.wait()
 r=dict(command=list(map(str,cmd)),returncode=p.returncode,seconds=time.monotonic()-start,peak_RSS_KiB=peak,killed=killed,cpu_limit_s=120,wall_limit_s=140,affinity_cpus=2)
 (W/'receipts'/f'{label}.json').write_text(json.dumps(r,indent=2)+'\n')
 if p.returncode!=expected or killed:raise RuntimeError(label+' failed; see logs')
 return r

run(sys.argv[1],sys.argv[2:])
