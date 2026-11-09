from pathlib import Path
import urllib.request,datetime,hashlib,json,resource,concurrent.futures,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent; (p/'sources').mkdir(exist_ok=True)
jobs=json.loads((p/'fetch-jobs.json').read_text())
def fetch(j):
 name,url=j; t=time.monotonic();r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=12) as f:
   b=f.read(20000000);r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(p/'sources'/name).write_bytes(b)
 except Exception as e:r['error']=str(e)
 r['wall_seconds']=time.monotonic()-t;return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex: out=list(ex.map(fetch,jobs))
(p/('receipts-'+str(int(time.time()))+'.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
