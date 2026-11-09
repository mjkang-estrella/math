import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,sys,urllib.request,datetime,time,threading
p=pathlib.Path(__file__).resolve().parent
samples=[]; stop=threading.Event()
def sample():
 while not stop.is_set():
  try:samples.append([time.monotonic(),int(pathlib.Path('/proc/self/statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')])
  except Exception:pass
  stop.wait(.05)
t=threading.Thread(target=sample);t.start();start=time.monotonic();code=0
try:
 for arg in sys.argv[1:]:
  name,url=arg.split('=',1);dest=(p/'sources'/name).resolve();assert dest.is_relative_to(p);dest.parent.mkdir(exist_ok=True)
  rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'actual_read':'acquired only until separately read'};begin=time.monotonic()
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'ResearchSourceReview/1.0'}),timeout=14) as r:
    b=r.read(12000000);rec.update(status=r.status,final_url=r.url,headers=dict(r.headers),bytes=len(b),sha256=hashlib.sha256(b).hexdigest());dest.write_bytes(b)
  except Exception as e:rec.update(error=repr(e),status=getattr(e,'code',None),final_url=getattr(e,'url',url),bytes=0,sha256=None)
  rec['wall_s']=time.monotonic()-begin;(p/'sources'/(name+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');print(name,json.dumps({k:v for k,v in rec.items() if k!='headers'}),flush=True)
except BaseException:code=1;raise
finally:
 stop.set();t.join();r=resource.getrusage(resource.RUSAGE_SELF);q=p/('resource-fetch-'+str(time.time_ns())+'.json');q.write_text(json.dumps({'body_true_exit':code,'wall_s':time.monotonic()-start,'CPU_s':r.ru_utime+r.ru_stime,'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit_s':120,'AS_bytes':6*1024**3,'sampled_self_RSS_bytes_max':max([s[1] for s in samples],default=0),'samples':len(samples),'self_peak_RSS_KiB':r.ru_maxrss,'children':0,'threads_joined':True,'limits':'sampled self only, not cgroup/group/transient guarantee'})+'\n')
