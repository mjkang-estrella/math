import resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024**2,64*1024**2))
import pathlib,json,urllib.request,urllib.error,hashlib,datetime,time,sys,os
L=pathlib.Path(__file__).resolve().parent
(L/'sources').mkdir(exist_ok=True)
for url in sys.argv[1:]:
 t=time.monotonic(); now=datetime.datetime.now(datetime.timezone.utc).isoformat(); key=hashlib.sha256(url.encode()).hexdigest()[:16]
 rec={'url':url,'utc':now,'affinity':sorted(os.sched_getaffinity(0)),'cpu_limit_s':120,'address_space_limit_bytes':6*1024**3,'wall_limit_external_s':140}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source qualification'}),timeout=18) as r:
   b=r.read(24*1024**2+1); assert len(b)<=24*1024**2
   rec.update(status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),artifact='sources/'+key+'.bin')
   (L/rec['artifact']).write_bytes(b)
 except Exception as e:rec.update(error=str(e),status=getattr(e,'code',None))
 rec.update(wall_s=time.monotonic()-t,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
 with (L/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec),flush=True)
