import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,urllib.request,datetime,time,concurrent.futures,sys
L=pathlib.Path(__file__).resolve().parent
jobs=json.loads(sys.argv[1])
def fetch(j):
 name,url=j; start=time.monotonic();r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'GET','read_depth':'acquired only'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-reader/1.0'}),timeout=10) as f:
   b=f.read(12*1024**2+1);assert len(b)<=12*1024**2;r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());p=(L/'sources'/name).resolve();assert p.is_relative_to(L);p.parent.mkdir(exist_ok=True);p.write_bytes(b)
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 r['wall_seconds']=time.monotonic()-start;print(json.dumps(r),flush=True);return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool: rows=list(pool.map(fetch,jobs))
p=(L/('fetch-receipt-'+datetime.datetime.now().strftime('%H%M%S%f')+'.json')).resolve();p.write_text(json.dumps({'jobs':rows,'exit':0,'all_threads_joined':True,'affinity':sorted(os.sched_getaffinity(0)),'self_rusage':list(resource.getrusage(resource.RUSAGE_SELF)),'telemetry':'self only, not group peak'},indent=2)+'\n')
