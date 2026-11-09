import resource,os,pathlib,urllib.request,hashlib,json,datetime,sys,time,concurrent.futures
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,)*2);os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=pathlib.Path(__file__).resolve().parent;(p/'sources').mkdir(exist_ok=True)
def fetch(pair):
 name,url=pair.split('=',1);start=time.monotonic();r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-review/1.0'}),timeout=22) as q:
   data=q.read(12000001);r.update(status=q.status,final_url=q.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());(p/'sources'/name).write_bytes(data)
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None),bytes=0,sha256=None)
 r.update(wall_seconds=time.monotonic()-start,read_depth='unread fetch',cpu_limit_seconds=120,address_space_limit_bytes=6*1024**3,cpu_affinity=sorted(os.sched_getaffinity(0)))
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex: rows=list(ex.map(fetch,sys.argv[1:]))
with (p/'http-receipts.jsonl').open('a') as f:
 for r in rows:f.write(json.dumps(r)+'\n');print(json.dumps(r))
print('REAPED',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
