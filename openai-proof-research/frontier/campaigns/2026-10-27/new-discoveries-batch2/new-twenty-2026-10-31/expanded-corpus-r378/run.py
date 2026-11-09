import os,resource,sys,subprocess,time,json,pathlib,datetime
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
lane=pathlib.Path(__file__).resolve().parent
code=sys.stdin.read();tag=sys.argv[1];start=time.monotonic();samples=[]
def run(args,data):
 p=subprocess.Popen(args,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True,text=True)
 import threading
 output={}
 def communicate(): output["v"]=p.communicate(data)
 t=threading.Thread(target=communicate);t.start()
 while t.is_alive():
  rss=0;pids=[]
  for q in pathlib.Path("/proc").iterdir():
   if not q.name.isdigit():continue
   try:
    st=(q/"stat").read_text().split();group=int(st[4])
    if group==p.pid:rss+=int(st[23])*os.sysconf("SC_PAGE_SIZE");pids.append(int(q.name))
   except (OSError,ValueError,IndexError):pass
  samples.append({"seconds":time.monotonic()-start,"rss_bytes":rss,"pids":pids})
  if rss>6*1024**3 or time.monotonic()-start>130:
   import signal
   os.killpg(p.pid,signal.SIGKILL)
  t.join(.05)
 t.join();p.wait();return p.returncode,output["v"]
rc,out=run([sys.executable,"-I","-B","-c","import os,resource;os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));\n"+code],code if False else None)
print(out[0],end="");print(out[1],file=sys.stderr,end="")
r={"tag":tag,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"exit":rc,"wall_seconds":time.monotonic()-start,"samples":samples,"children_reaped":True,"rusage_children":list(resource.getrusage(resource.RUSAGE_CHILDREN)),"limitations":"sampled RSS may miss short-lived descendants; cumulative child rusage; first inspection before runner had limits but no sampled group telemetry"}
wrc,wout=run([sys.executable,"-I","-B",str(lane/"write_lane.py"),"resources/"+tag+".json"],json.dumps(r,indent=2));print("RECEIPT",tag,rc,wrc);sys.exit(rc)
