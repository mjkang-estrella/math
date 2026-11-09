import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,time,json,hashlib,subprocess,threading,datetime,urllib.request,urllib.error
from pathlib import Path
P=Path(__file__).resolve().parent
start=time.monotonic(); samples=[]; stop=threading.Event()
def sample():
 while not stop.wait(.05):
  try:
   s=Path('/proc/self/status').read_text();rss=int(s.split('VmRSS:')[1].split()[0]);samples.append(rss)
   if rss>5*1024**2:os._exit(97)
  except (OSError,IndexError):pass
t=threading.Thread(target=sample);t.start()
def write(n,s):
 r=subprocess.run([sys.executable,'-I','-B',str(P/'write_lane.py'),n],input=s,text=True,capture_output=True,timeout=20)
 assert r.returncode==0,r.stderr
 return {'path':n,'writer_exit':r.returncode,'bytes':len(s.encode()),'sha256':hashlib.sha256(s.encode()).hexdigest()}
def dump(n,v):return write(n,json.dumps(v,ensure_ascii=False,indent=2)+'\n')
out=[]
try:
 for i,url in enumerate(sys.argv[1:]):
  rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'read_depth':'acquired only'}
  try:
   with urllib.request.urlopen(url,timeout=15) as r:
    b=r.read(8000000);rec.update(status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),headers=dict(r.headers))
   name='sources/url-'+hashlib.sha256(url.encode()).hexdigest()[:12]+'.html';write(name,b.decode());rec['path']=name;print(url,rec['status'],len(b),name)
  except Exception as e:rec.update(error=str(e),status=getattr(e,'code',None));print(url,str(e))
  out.append(rec)
 dump('http-urls-'+str(time.time_ns())+'.json',out)
finally:
 stop.set();t.join();u=resource.getrusage(resource.RUSAGE_SELF)
 dump('resource-'+str(time.time_ns())+'.json',{'argv':sys.argv,'wall_s':time.monotonic()-start,'self_CPU_s':u.ru_utime+u.ru_stime,'self_peak_RSS_KiB':u.ru_maxrss,'sampled_self_RSS_max_KiB':max(samples,default=None),'RSS_guard_KiB':5*1024**2,'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit':120,'AS_limit':6*1024**3,'external_wall_cap':140,'scope':'self sampling; writer children joined, not group telemetry','exception':str(sys.exc_info()[1]) if sys.exc_info()[0] else None})
