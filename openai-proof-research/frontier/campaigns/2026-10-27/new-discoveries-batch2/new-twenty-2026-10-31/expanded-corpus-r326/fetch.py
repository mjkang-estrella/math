import os,resource,pathlib,json,time,hashlib,urllib.request,sys,datetime
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).parent;t=time.monotonic(); receipts=[];(p/'sources').mkdir(exist_ok=True)
for url in sys.argv[1:]:
 r={'url':url,'method':'GET','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=18) as f:
   b=f.read(12000001);assert len(b)<=12000000
   name=hashlib.sha256(url.encode()).hexdigest()[:16]+('.pdf' if b.startswith(b'%PDF') else '.html');(p/'sources'/name).write_bytes(b)
   r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),path='sources/'+name)
 except Exception as e:r['error']=str(e)
 receipts.append(r);print(json.dumps(r),flush=True)
old=json.loads((p/'http-receipts.json').read_text()) if (p/'http-receipts.json').exists() else []
(p/'http-receipts.json').write_text(json.dumps(old+receipts,indent=2))
ru=resource.getrusage(resource.RUSAGE_SELF);f=p/'resource-jobs.jsonl'
with f.open('a') as o:o.write(json.dumps({'job':'fetch','wall_s':time.monotonic()-t,'self_CPU_s':ru.ru_utime+ru.ru_stime,'self_highwater_RSS_KiB':ru.ru_maxrss,'affinity':sorted(os.sched_getaffinity(0)),'AS_limit':6*1024**3,'CPU_limit':120,'group_RSS':'unavailable','all_requests_synchronous':True})+'\n')
