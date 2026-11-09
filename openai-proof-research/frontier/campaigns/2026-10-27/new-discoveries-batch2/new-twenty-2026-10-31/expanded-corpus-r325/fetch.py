import os,resource,pathlib,json,hashlib,time,urllib.request,sys,datetime
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).parent
start=time.monotonic(); receipts=[]
for label,url in json.loads(sys.argv[1]):
 r={"label":label,"url":url,"method":"GET","utc":datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={"User-Agent":"Research source reading"}),timeout=12) as f:
   b=f.read(12000000);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(p/(label+".raw")).write_bytes(b)
 except Exception as e:r.update(error=str(e))
 receipts.append(r);print(json.dumps(r),flush=True)
(p/("http-"+str(time.time_ns())+".json")).write_text(json.dumps({"receipts":receipts,"wall_s":time.monotonic()-start,"affinity":sorted(os.sched_getaffinity(0)),"self_cpu_s":resource.getrusage(resource.RUSAGE_SELF).ru_utime+resource.getrusage(resource.RUSAGE_SELF).ru_stime,"self_peak_rss_KiB":resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,"group_sampled_rss":"unavailable"},indent=2))
