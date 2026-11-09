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
try:
 mode=sys.argv[1]; out=[]
 if mode=='history':
  rows=json.loads((P/'raw-records.json').read_text()); ids=list(rows)
  allow=json.loads((P/'historical-results-allowlist.json').read_text()); inv=[];matches=[]
  needles=ids+['2104.05598','2108.04995','2109.13637','2106.14042','2104.09009','2105.00185','2109.01180','2109.15145','2106.05685']
  for name in allow:
   if any(x in name.lower() for x in ['crown','transitive-bunkbed','tournament-update-lower']):continue
   f=Path(name)
   try:b=f.read_bytes()
   except OSError as e:inv.append({'path':name,'error':str(e)});continue
   inv.append({'path':name,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'depth':'completed result file only'})
   text=b.decode()
   if any(x in text for x in needles):matches.append({'path':name,'body':json.loads(text)})
  dump('historical-comparison.json',{'inventory':inv,'matches':matches,'filter':'protected names filtered lexically BEFORE opening; exact allowlist only'})
  for x in matches:print(json.dumps(x,ensure_ascii=False))
 elif mode=='fetch':
  for ident in sys.argv[2:]:
   url='https://arxiv.org/html/'+ident
   rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'read_depth':'acquired only'}
   try:
    with urllib.request.urlopen(url,timeout=15) as r:
     b=r.read(8000000);rec.update(status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
    rec['artifact']=write('sources/'+ident+'.html',b.decode());print('FETCH',ident,rec['status'],len(b))
   except Exception as e:rec.update(error=str(e),status=getattr(e,'code',None));print('FAIL',ident,str(e))
   out.append(rec)
  dump('http-'+str(time.time_ns())+'.json',out)
finally:
 stop.set();t.join();u=resource.getrusage(resource.RUSAGE_SELF)
 dump('resource-'+str(time.time_ns())+'.json',{'argv':sys.argv,'wall_s':time.monotonic()-start,'self_CPU_s':u.ru_utime+u.ru_stime,'self_peak_RSS_KiB':u.ru_maxrss,'sampled_self_RSS_max_KiB':max(samples,default=None),'RSS_guard_KiB':5*1024**2,'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit':120,'AS_limit':6*1024**3,'external_wall_cap':140,'scope':'self sampling; writer children joined, not group telemetry','exception':str(sys.exc_info()[1]) if sys.exc_info()[0] else None})
