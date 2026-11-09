import json,sys,hashlib,datetime,resource,time,concurrent.futures,urllib.request,urllib.error
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent.parent
(p/'sources').mkdir(exist_ok=True)
jobs=json.loads(Path(sys.argv[1]).read_text())
def fetch(job):
 name,url=job; r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'ResearchSourceReview/1.0'}),timeout=8) as f:
   data=f.read(20*1024**2);r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(p/'sources'/name).write_bytes(data)
 except Exception as e:r.update(error=str(e))
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(fetch,jobs):
  with (p/'receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(json.dumps(r),flush=True)
