import os,resource,time,pathlib,json,hashlib,urllib.request,urllib.error,concurrent.futures,sys,atexit
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).parent
start=time.monotonic()
receipts=[]
def fetch(item):
 name,url=item;utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());r={'url':url,'utc':utc,'method':'GET','name':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'ordinary-math-research/1.0'}),timeout=22) as f:
   b=f.read(15000000);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(p/name).write_bytes(b)
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None),bytes=0)
 receipts.append(r);return r
items=json.loads(sys.argv[1])
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(fetch,items):print(json.dumps(r),flush=True)
with (p/'http-receipts.jsonl').open('a') as f:
 for r in receipts:f.write(json.dumps(r)+'\n')
with (p/'resource-jobs.jsonl').open('a') as f:f.write(json.dumps({'job':'fetch','items':items,'elapsed':time.monotonic()-start,'self_rusage':list(resource.getrusage(resource.RUSAGE_SELF)),'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit':120,'AS_limit':6*1024**3,'group_RSS':'unavailable','exit':0})+'\n')
