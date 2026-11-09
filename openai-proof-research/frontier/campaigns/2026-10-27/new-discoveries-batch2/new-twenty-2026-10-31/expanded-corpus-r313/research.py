import os,resource,time,pathlib,json,hashlib,urllib.request,concurrent.futures,sys
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).resolve().parent
start=time.time(); receipts=[]
def fetch(job):
 name,url=job;stamp=time.time();rec={'url':url,'utc_epoch':stamp,'local':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source review'}),timeout=12) as f:
   b=f.read(12000000);rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(p/name).parent.mkdir(exist_ok=True);(p/name).write_bytes(b)
 except Exception as e:rec.update(error=str(e))
 rec['wall_seconds']=time.time()-stamp;return rec
jobs=json.loads((p/sys.argv[1]).read_text())
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for rec in ex.map(fetch,jobs):receipts.append(rec);print(json.dumps(rec),flush=True)
(p/(sys.argv[1]+'.receipts.json')).write_text(json.dumps(receipts,indent=2))
u=resource.getrusage(resource.RUSAGE_SELF)
(p/(sys.argv[1]+'.process.json')).write_text(json.dumps({'argv':sys.argv,'affinity':sorted(os.sched_getaffinity(0)),'cpu_limit':120,'as_limit':6*1024**3,'wall_limit_external':140,'wall_seconds':time.time()-start,'user_seconds':u.ru_utime,'system_seconds':u.ru_stime,'peak_rss_KiB':u.ru_maxrss,'threads':2,'reaped':True},indent=2))
