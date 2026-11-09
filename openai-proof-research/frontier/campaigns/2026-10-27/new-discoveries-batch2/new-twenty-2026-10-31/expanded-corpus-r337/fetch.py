import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,urllib.request,datetime,sys
p=pathlib.Path(__file__).resolve().parent
def write(name,b):
 q=(p/name).resolve(); assert q.is_relative_to(p); q.parent.mkdir(parents=True,exist_ok=True); q.write_bytes(b if isinstance(b,bytes) else b.encode())
def fetch(url,name):
 t=time.monotonic(); rec={"url":url,"UTC":datetime.datetime.now(datetime.timezone.utc).isoformat(),"method":"GET"}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={"User-Agent":"research-source-review/1.0"}),timeout=18) as f:
   b=f.read(16000001); assert len(b)<=16000000
   rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()); write(name,b)
 except Exception as e:rec.update(error=str(e),status=getattr(e,"code",None))
 rec["wall_seconds"]=time.monotonic()-t
 write(name+".receipt.json",json.dumps(rec,indent=2)+"\n"); print(json.dumps(rec),flush=True)
for url,name in json.loads(sys.argv[1]):fetch(url,name)
write("resource-"+sys.argv[2]+".json",json.dumps({"exit":0,"affinity":sorted(os.sched_getaffinity(0)),"CPU_limit":120,"wall_limit":140,"AS_limit":6*1024**3,"self_rusage":list(resource.getrusage(resource.RUSAGE_SELF)),"children":0,"limitation":"self high-water RSS; not simultaneous group peak"}))
