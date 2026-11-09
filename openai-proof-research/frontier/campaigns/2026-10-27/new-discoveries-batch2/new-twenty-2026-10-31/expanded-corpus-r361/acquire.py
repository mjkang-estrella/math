import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,time,datetime,hashlib,urllib.request,concurrent.futures,sys
L=pathlib.Path(__file__).resolve().parent; start=time.monotonic(); run=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f')
def wr(p,b):
 p=(L/p).resolve(); assert p.is_relative_to(L); p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(b)
def one(pair):
 url,name=pair; rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),method='GET',depth='acquired, not read')
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Bounded public mathematical research'}),timeout=20) as r:
   b=r.read(12000001); assert len(b)<=12000000; rec.update(status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),artifact='sources/'+name); wr('sources/'+name,b)
 except Exception as e: rec.update(status=getattr(e,'code',None),error=repr(e))
 return rec
pairs=json.loads(sys.argv[1]); code=0
try:
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
  results=list(ex.map(one,pairs))
 wr('receipts/http-batch-'+run+'.json',(json.dumps(results,indent=2)+'\n').encode()); print(json.dumps(results))
except: code=1; raise
finally:
 u=resource.getrusage(resource.RUSAGE_SELF); wr('receipts/process-acquire-'+run+'.json',(json.dumps(dict(exit_code=code,wall_s=time.monotonic()-start,affinity=sorted(os.sched_getaffinity(0)),CPU_limit=120,AS_limit=6*1024**3,self_peak_RSS_KiB=u.ru_maxrss,self_CPU_s=u.ru_utime+u.ru_stime,threads_joined=True,external_wall_timeout=140,limitation='Self high-water, not sampled group peak'))+'\n').encode())
