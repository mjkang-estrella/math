import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,)*2)
import sys,json,urllib.request,hashlib,time,concurrent.futures,datetime
from pathlib import Path
p=Path(__file__).parent
def fetch(item):
 name,url=item;t=time.monotonic();rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source reading'}),timeout=25) as f:
   b=f.read(16000001);rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(p/'sources'/name).write_bytes(b)
 except Exception as e:rec['error']=str(e)
 rec['wall_seconds']=time.monotonic()-t;return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:out=list(ex.map(fetch,json.loads(sys.argv[1])))
with (p/'http-receipts.jsonl').open('a') as f:
 for x in out:f.write(json.dumps(x)+'\n')
print(json.dumps(out,indent=2));print('telemetry',{'affinity':sorted(os.sched_getaffinity(0)),'cpu':resource.getrusage(resource.RUSAGE_SELF).ru_utime+resource.getrusage(resource.RUSAGE_SELF).ru_stime,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'all_threads_joined':True})
