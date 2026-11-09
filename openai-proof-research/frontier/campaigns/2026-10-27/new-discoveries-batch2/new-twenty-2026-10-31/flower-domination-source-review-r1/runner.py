import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,pathlib,json,time,hashlib,subprocess,threading,urllib.request
LANE=pathlib.Path(__file__).resolve().parent
events=[];start=time.time(); peaks=[]
def write(name,text):
 p=subprocess.Popen([sys.executable,"-I","-B",str(LANE/"write_lane.py"),name],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
 peak=[0];stop=threading.Event()
 def guard():
  while not stop.is_set():
   try:
    rss=int(pathlib.Path("/proc/"+str(p.pid)+"/status").read_text().split("VmRSS:")[1].split()[0])*1024
    peak[0]=max(peak[0],rss)
    if rss>512*1024**2:p.kill()
   except (FileNotFoundError,IndexError,ProcessLookupError):pass
   stop.wait(.005)
 t=threading.Thread(target=guard);t.start()
 out,err=p.communicate(text);stop.set();t.join();peaks.append({"pid":p.pid,"exit":p.returncode,"peak_sampled_RSS_bytes":peak[0],"stderr":err})
 if p.returncode:raise RuntimeError(err)
def read(path):
 b=pathlib.Path(path).read_bytes();events.append({"operation":"read","path":path,"time":time.time(),"bytes":len(b),"sha256":hashlib.sha256(b).hexdigest()})
 print("FILE",path,flush=True);print(b.decode(),flush=True)
def main():
 req=json.load(sys.stdin)
 for path in req.get("reads",[]):read(path)
 for item in req.get("gets",[]):
  url=item["url"];e={"operation":"GET","url":url,"time":time.time()};events.append(e)
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={"User-Agent":"source-review/1.0"}),timeout=25) as r:b=r.read();e.update(status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
   if item.get("save"):write(item["save"],b.decode())
   print("GET",json.dumps(e),flush=True)
   if item.get("show",True):print(b.decode(errors="replace"),flush=True)
  except Exception as ex:e["error"]=repr(ex);print(json.dumps(e),flush=True)
 for n,t in req.get("writes",{}).items():write(n,t)
label=sys.argv[1];code=0
try:main()
except BaseException as ex:code=1;events.append({"error":repr(ex)});raise
finally:
 u=resource.getrusage(resource.RUSAGE_SELF)
 rec={"label":label,"start":start,"end":time.time(),"events":events,"true_exit_intended":code,"self_peak_RSS_KiB":u.ru_maxrss,"self_CPU_s":u.ru_utime+u.ru_stime,"affinity":sorted(os.sched_getaffinity(0)),"CPU_limit":120,"AS_limit":6*1024**3,"external_wall_timeout":140,"writer_children":peaks,"no_other_descendants":True}
 write("receipt-"+label+".json",json.dumps(rec,indent=2)+"\n")
