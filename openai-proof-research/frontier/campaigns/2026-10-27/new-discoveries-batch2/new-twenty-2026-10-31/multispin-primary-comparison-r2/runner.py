import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,json,time,hashlib,pathlib,subprocess,urllib.request,datetime,signal
L=pathlib.Path(__file__).resolve().parent
records=[]
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def child(args,data=None):
 p=subprocess.Popen(args,stdin=subprocess.PIPE if data is not None else subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
 import threading
 result=[]
 worker=threading.Thread(target=lambda:result.append(p.communicate(data)));worker.start()
 samples=[];start=time.monotonic()
 while p.poll() is None:
  ids=[p.pid];rss=0
  for pid in ids:
   try:
    ids.extend(int(v) for v in pathlib.Path(f'/proc/{pid}/task/{pid}/children').read_text().split())
    st=pathlib.Path(f'/proc/{pid}/status').read_text()
    rss+=int(next((x.split()[1] for x in st.splitlines() if x.startswith('VmRSS:')),'0'))
   except FileNotFoundError: pass
  samples.append({'pids':ids,'rss_kib':rss})
  if rss>6*1024**2 or time.monotonic()-start>125: os.killpg(p.pid,signal.SIGKILL)
  time.sleep(.005)
 worker.join();out,err=result[0];records.append({'kind':'child','argv':args,'utc':now(),'exit':p.returncode,'reaped':True,'rss_samples':samples,'stderr':err.decode(errors='replace')})
 if p.returncode: raise RuntimeError(err.decode(errors='replace'))
 return out

def write(name,text):
 return child([sys.executable,'-I','-B',str(L/'write_lane.py'),name],text.encode()).decode()

def read(path):
 b=pathlib.Path(path).read_bytes();records.append({'kind':'read','path':str(path),'utc':now(),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)});return b.decode()
def fetch(url,name):
 r={'kind':'GET','url':url,'utc':now()};records.append(r)
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-review/1.0'}),timeout=35) as f:
   b=f.read(12*1024**2);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  import base64
  write(name+'.base64',base64.b64encode(b).decode())
  return b
 except Exception as e:r.update(error=repr(e));return None
start=time.monotonic()
try:
 exec(sys.stdin.read())
finally:
 records.append({'kind':'resource','utc':now(),'pid':os.getpid(),'affinity':sorted(os.sched_getaffinity(0)),'cpu_limit':120,'as_bytes':6*1024**3,'self_cpu_s':resource.getrusage(resource.RUSAGE_SELF).ru_utime+resource.getrusage(resource.RUSAGE_SELF).ru_stime,'self_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'wall_s':time.monotonic()-start,'caps_before_reads':True})
 print('RECEIPTS',json.dumps(records))
 # This write's child telemetry is printed after it completes, not falsely included in its own persisted receipt.
 n='receipt-'+str(time.time_ns())+'.json'
 write(n,json.dumps(records,indent=2)+'\n');print('RECEIPT_WRITE',json.dumps(records[-1]));print('SAVED',n)
