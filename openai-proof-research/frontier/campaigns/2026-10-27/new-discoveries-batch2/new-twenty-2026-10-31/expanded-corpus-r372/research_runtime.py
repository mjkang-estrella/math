import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,subprocess,json,time,hashlib,sys,threading,datetime,base64,urllib.request
L=pathlib.Path("/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r372")
START=time.monotonic(); READS=[]; JOBS=[]; HTTP=[]
def read(p):
 p=pathlib.Path(p); b=p.read_bytes(); READS.append(dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),depth="full byte read; semantic review only as separately identified",utc=datetime.datetime.now(datetime.timezone.utc).isoformat()));return b
def child(args,data):
 p=subprocess.Popen(args,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE); peaks={}; stop=threading.Event()
 def sample():
  while not stop.is_set():
   try:
    todo=[p.pid];total=0
    while todo:
     pid=todo.pop()
     try:
      status=pathlib.Path(f"/proc/{pid}/status").read_text(); rss=int(status.split("VmRSS:")[1].split()[0]) if "VmRSS:" in status else 0;total+=rss;peaks[pid]=max(peaks.get(pid,0),rss)
      todo+=list(map(int,pathlib.Path(f"/proc/{pid}/task/{pid}/children").read_text().split()))
     except (FileNotFoundError,ProcessLookupError):pass
    if total>6*1024**2:p.kill()
   except Exception:pass
   stop.wait(.01)
 t=threading.Thread(target=sample);t.start()
 try:o,e=p.communicate(data,timeout=130)
 except subprocess.TimeoutExpired:p.kill();o,e=p.communicate()
 finally:stop.set();t.join()
 JOBS.append(dict(argv=args,exit=p.returncode,sampled_RSS_KiB_by_pid=peaks,reaped=True,stderr=e.decode(errors="replace")));assert p.returncode==0,(args,e);return o
def write(name,s):
 if not isinstance(s,str):s=json.dumps(s,indent=2,ensure_ascii=False)+"\n"
 return child([sys.executable,"-I","-B",str(L/"write_lane.py"),name],s.encode())
def finish(tag):
 u=resource.getrusage(resource.RUSAGE_SELF)
 write("receipts/"+tag+".json",dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),reads=READS,jobs=JOBS.copy(),HTTP=HTTP,affinity=sorted(os.sched_getaffinity(0)),CPU_limit=120,AS_limit=6*1024**3,wall=time.monotonic()-START,self_peak_RSS_KiB=u.ru_maxrss,self_CPU=u.ru_utime+u.ru_stime,reader_exit_note="normal completion reaches receipt; external tool exit separately observed; receipt writer cannot attest its own exit",limits="10ms sampled descendant RSS for spawned writers/converters; self highwater is not group telemetry"))
def fetch(url,name):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={"User-Agent":"Research source fidelity (public GET)"}),timeout=30) as r:b=r.read(); status=r.status; final=r.url
  HTTP.append(dict(url=url,utc=t,status=status,finalURL=final,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),read_depth="acquired full bytes; see semantic inventory"))
  if b.startswith(b"%PDF"):
   write("sources/"+name+".pdf.base64",base64.b64encode(b).decode());s=child(["pdftotext","-layout","-","-"],b).decode()
  else:s=b.decode(errors="replace")
  write("sources/"+name+".txt",s);return s
 except Exception as e:HTTP.append(dict(url=url,utc=t,error=str(e),read_depth="failed; no clearance"));return ""
