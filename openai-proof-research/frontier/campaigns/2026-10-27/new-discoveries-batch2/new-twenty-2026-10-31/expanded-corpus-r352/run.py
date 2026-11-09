import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,sys,datetime,atexit,urllib.request,concurrent.futures,html,re
P=pathlib.Path(__file__).resolve().parent
start=time.monotonic(); run=str(time.time_ns()); reads=[]; accesses=[]
def put(n,data):
 p=(P/n).resolve(); assert p.is_relative_to(P); p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(data if isinstance(data,bytes) else data.encode())
def js(n,x):put(n,json.dumps(x,ensure_ascii=False,indent=2)+"\n")
def read(p):
 b=pathlib.Path(p).read_bytes();reads.append({"path":str(p),"bytes":len(b),"sha256":hashlib.sha256(b).hexdigest()});return b
def finish():
 js("receipts/run-"+run+".json",{"argv":sys.argv,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"affinity":sorted(os.sched_getaffinity(0)),"cpu_cap":120,"as_cap":6*1024**3,"wall_cap":140,"wall":time.monotonic()-start,"self_rusage":list(resource.getrusage(resource.RUSAGE_SELF)),"limitation":"Self peak RSS, not concurrent group peak. No child processes.","reads":reads,"accesses":accesses,"exit":getattr(sys,"last_exit",0)})
old_finish=finish
def finish():
 old_finish()
 if globals().get("FINALIZE",False):
  manifest={}
  for p in sorted(P.rglob("*")):
   if p.is_file() and p.name not in ["manifest.json","manifest-verification.json"]:
    assert "crown" not in str(p.relative_to(P)).lower()
    data=p.read_bytes();manifest[str(p.relative_to(P))]={"bytes":len(data),"sha256":hashlib.sha256(data).hexdigest()}
  js("manifest.json",manifest)
  errors=[]
  for n,item in manifest.items():
   data=(P/n).read_bytes()
   if len(data)!=item["bytes"] or hashlib.sha256(data).hexdigest()!=item["sha256"]:errors.append(n)
  js("manifest-verification.json",{"verified":not errors,"artifact_count":len(manifest),"errors":errors,"manifest_sha256":hashlib.sha256((P/"manifest.json").read_bytes()).hexdigest(),"exclusions":["manifest.json","manifest-verification.json"],"no_live_children":True,"telemetry_scope":"self only; no children launched"})
atexit.register(finish)
def fetch(url,name):
 r={"url":url,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"method":"GET","name":name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={"User-Agent":"Research source review"}),timeout=35) as q:
   b=q.read(20000000);r.update(status=q.status,final_url=q.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());put("sources/"+name,b)
 except Exception as e:r.update(error=str(e))
 accesses.append(r);return r
try:
 exec(compile(sys.argv[2] if sys.argv[1]=="-c" else read(P/sys.argv[1]),"lane-code","exec"))
except BaseException:
 sys.last_exit=1;raise
