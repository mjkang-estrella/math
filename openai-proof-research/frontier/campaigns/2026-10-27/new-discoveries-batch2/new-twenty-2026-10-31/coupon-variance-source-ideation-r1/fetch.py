import os,sys,pathlib,json,urllib.request,datetime,hashlib,resource,time
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).parent;(p/'sources').mkdir(exist_ok=True)
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};t=time.monotonic()
 try:
  with urllib.request.urlopen(url,timeout=25) as f:
   data=f.read(16000000);r.update(status=f.status,final_url=f.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());(p/'sources'/name).write_bytes(data)
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 r.update(wall_seconds=time.monotonic()-t,maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,affinity=sorted(os.sched_getaffinity(0)))
 with (p/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r),flush=True)
