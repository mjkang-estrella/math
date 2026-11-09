import os,subprocess,resource,time,json
from pathlib import Path
base=Path(__file__).resolve().parent
m=Path("/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages")
env=dict(os.environ)
env["LEAN_PATH"]=":".join(str(p/".lake/build/lib/lean") for p in m.iterdir() if p.is_dir())
env["LEAN_NUM_THREADS"]="1"
env["MALLOC_ARENA_MAX"]="2"
lean="/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean"
def cap():
 os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
 resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,4*1024**3))
 resource.setrlimit(resource.RLIMIT_CORE,(0,0))
with (base/"lean.log").open("w") as log:
 p=subprocess.Popen([lean,"-M","256","-j","1","-s","512",str(base/"ArithmeticStart.lean")],env=env,cwd=base,stdout=log,stderr=subprocess.STDOUT,preexec_fn=cap)
 peak=0; killed=False
 while p.poll() is None:
  try:
   status=Path(f"/proc/{p.pid}/status").read_text()
   rss=int(status.split("VmRSS:")[1].split()[0]);peak=max(peak,rss)
   if rss>470*1024:p.kill();killed=True
  except (FileNotFoundError,IndexError):pass
  time.sleep(0.001)
 code=p.wait()
receipt={"returncode":code,"rss_kill_threshold_kib":470*1024,"observed_max_rss_kib":peak,"rss_killed":killed,"address_space_limit_bytes":4*1024**3,"lean_memory_mb":256}
(base/"lean-receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
print((base/"lean.log").read_text());print(receipt)
