import os,resource,pathlib,json,hashlib,urllib.request,datetime,time,sys
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).parent
start=time.monotonic()
for name,url in json.loads(sys.argv[1]):
 r={"url":url,"method":"GET","utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"name":name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={"User-Agent":"Research source reader"}),timeout=22) as f:
   b=f.read(20000001);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());assert len(b)<=20000000
   (p/name).write_bytes(b)
 except Exception as e:r["error"]=str(e)
 with (p/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r),flush=True)
 if time.monotonic()-start>105:break
print("RESOURCE",json.dumps({"affinity":sorted(os.sched_getaffinity(0)),"wall_s":time.monotonic()-start,"self_peak_RSS_KiB":resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,"group_sampled_RSS":"unavailable"}))
