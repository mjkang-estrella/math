import urllib.request,json,hashlib,datetime,resource,os,sys
from pathlib import Path
p=Path(__file__).resolve().parent
(p/'sources').mkdir(exist_ok=True)
def fetch(url,name):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'name':name,'read_depth':'retrieved_only'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source qualification'}),timeout=8) as f:
   b=f.read(16000001); r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()); (p/'sources'/name).write_bytes(b)
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None),bytes=0)
 with (p/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(name,r.get('status'),r.get('bytes'),r.get('error',''),flush=True)
for url,name in json.loads(sys.argv[1]):fetch(url,name)
with (p/'resource-log.jsonl').open('a') as f:f.write(json.dumps({'stage':'fetch','affinity':sorted(os.sched_getaffinity(0)),'cpu_limits':resource.getrlimit(resource.RLIMIT_CPU),'as_limits':resource.getrlimit(resource.RLIMIT_AS),'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'pid':os.getpid()})+'\n')
