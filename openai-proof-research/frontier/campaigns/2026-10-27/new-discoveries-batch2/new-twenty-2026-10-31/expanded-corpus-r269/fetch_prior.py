from pathlib import Path
import json,urllib.request,hashlib,datetime,resource,concurrent.futures
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;s=p/'sources';s.mkdir(exist_ok=True)
rows=json.loads((p/'extracted-records.json').read_text())
jobs=[('fink.pdf','https://arxiv.org/pdf/1106.1883'),('manon.pdf','https://arxiv.org/pdf/1107.3668'),('hamilton.pdf','https://arxiv.org/pdf/1202.6219'),('dominated.html','https://www.sciencedirect.com/science/article/pii/S0012365X19304765')]
def fetch(job):
 name,url=job;r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':str(s/name)}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source review'}),timeout=10) as q:
   b=q.read(12*1024**2);r.update(status=q.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(s/name).write_bytes(b)
 except Exception as e:r['error']=str(e)
 (s/(name+'.receipt.json')).write_text(json.dumps(r,indent=2)+'\n');return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for r in pool.map(fetch,jobs):print(json.dumps(r),flush=True)
