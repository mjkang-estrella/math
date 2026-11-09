import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,sys,json,urllib.request,datetime,hashlib,time,subprocess
p=pathlib.Path(__file__).parent
start=time.monotonic()
for arg in sys.argv[1:]:
 name,u=arg.split("=",1)
 r={"url":u,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"method":"GET"}
 try:
  with urllib.request.urlopen(u,timeout=12) as f:
   b=f.read(15000000);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  q=p/"sources"/name;q.write_bytes(b);r["file"]=str(q)
  if b.startswith(b"%PDF"):r["pdftotext_exit"]=subprocess.run(["pdftotext","-layout",str(q),str(q)+".txt"],timeout=20,capture_output=True).returncode
 except Exception as e:r["error"]=str(e)
 with (p/"http-receipts.jsonl").open("a") as f:f.write(json.dumps(r)+"\n")
 print(json.dumps(r))
r={"argv":sys.argv,"exit":0,"wall_seconds":time.monotonic()-start,"self_rusage":list(resource.getrusage(resource.RUSAGE_SELF)),"reaped_child_rusage":list(resource.getrusage(resource.RUSAGE_CHILDREN)),"group_or_service_telemetry":"unavailable","cpus":sorted(os.sched_getaffinity(0)),"cpu_cap":120,"as_cap":6*1024**3}
with (p/"jobs.jsonl").open("a") as f:f.write(json.dumps(r)+"\n")
