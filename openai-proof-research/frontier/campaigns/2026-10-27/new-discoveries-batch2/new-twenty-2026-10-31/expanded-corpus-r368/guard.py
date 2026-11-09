import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,subprocess,time,json,pathlib,hashlib,threading,datetime
L=pathlib.Path(__file__).resolve().parent
start=time.monotonic(); peak=0; killed=False; samples=0
p=subprocess.Popen([sys.executable,"-I","-B",str(L/"research.py"),*sys.argv[1:]])
while p.poll() is None:
 ids={p.pid}; rows={}
 for f in pathlib.Path("/proc").iterdir():
  if f.name.isdigit():
   try:
    st=(f/"status").read_text(); d={a:b.strip() for a,b in (x.split(":",1) for x in st.splitlines() if ":" in x)};rows[int(f.name)]=(int(d["PPid"]),int(d.get("VmRSS","0 kB").split()[0]))
   except (OSError,ValueError,KeyError):pass
 for _ in range(5):ids|={i for i,(parent,rss) in rows.items() if parent in ids}
 rss=sum(rows.get(i,(0,0))[1] for i in ids);peak=max(peak,rss);samples+=1
 if rss>5*1024**2 or time.monotonic()-start>125:
  killed=True
  for i in ids:
   try:os.kill(i,9)
   except ProcessLookupError:pass
 time.sleep(.02)
rc=p.wait()
r={"action":sys.argv[1:],"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"exit":rc,"wall_s":time.monotonic()-start,"sampled_descendant_peak_RSS_KiB":peak,"samples":samples,"RSS_kill_threshold_KiB":5*1024**2,"killed":killed,"CPU_limit_s":120,"AS_bytes":6*1024**3,"affinity":sorted(os.sched_getaffinity(0)),"limitation":"20ms sampled descendant sum, not transient/cgroup peak; child reaped; inherited limits before script reads"}
name="resource-"+str(time.time_ns())+".json"
q=subprocess.run([sys.executable,"-I","-B",str(L/"write_lane.py"),name],input=json.dumps(r,indent=2)+"\n",text=True);assert q.returncode==0
print(json.dumps(r));sys.exit(rc)
