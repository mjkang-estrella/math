import os,resource,sys,pathlib,json,time,hashlib,urllib.request,urllib.error
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).parent
url=sys.argv[1];name=sys.argv[2];start=time.time();r={"url":url,"utc":time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime()),"method":"GET","caps":{"cpus":list(os.sched_getaffinity(0)),"cpu_s":120,"AS_bytes":6*1024**3,"external_wall_s":140}}
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={"User-Agent":"Research source reading"}),timeout=35) as f:
  b=f.read(18000000);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(p/"sources"/name).write_bytes(b)
except Exception as e:r.update(error=str(e))
r.update(elapsed_s=time.time()-start,self_rusage=list(resource.getrusage(resource.RUSAGE_SELF)),telemetry="Self high-water only; group/cgroup/service RSS unavailable")
with (p/"http-receipts.jsonl").open("a") as f:f.write(json.dumps(r)+"\n")
print(json.dumps(r))
