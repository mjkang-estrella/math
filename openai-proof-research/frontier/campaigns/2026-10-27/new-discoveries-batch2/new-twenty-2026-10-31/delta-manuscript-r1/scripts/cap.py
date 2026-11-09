import os,sys,subprocess,resource,time,signal,json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
os.environ.update(MALLOC_ARENA_MAX="2",TMPDIR=str(root/"tmp"),PYTHONDONTWRITEBYTECODE="1")
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6000000000,6000000000));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
t=time.monotonic();p=subprocess.Popen(sys.argv[1:],cwd=root,env=os.environ,preexec_fn=limits,start_new_session=True);peak=0;reason=None
while p.poll() is None:
 rss=0
 for q in Path("/proc").iterdir():
  if not q.name.isdigit():continue
  try:
   if os.getpgid(int(q.name))==p.pid:
    for line in (q/"status").read_text().splitlines():
     if line.startswith("VmRSS:"):rss+=int(line.split()[1])*1024
  except (OSError,ProcessLookupError):pass
 peak=max(peak,rss)
 if rss>=6*1024**3 or time.monotonic()-t>=139:
  reason="RSS" if rss>=6*1024**3 else "wall";os.killpg(p.pid,signal.SIGKILL);break
 time.sleep(.05)
code=p.wait();r={"command":sys.argv[1:],"exit":code,"wall_seconds":time.monotonic()-t,"sampled_group_peak_RSS_bytes":peak,"kill_reason":reason,"cpus":len(os.sched_getaffinity(0))}
with (root/"receipts/resources.jsonl").open("a") as f:f.write(json.dumps(r)+"\n")
sys.exit(code if code>=0 else 128-code)
