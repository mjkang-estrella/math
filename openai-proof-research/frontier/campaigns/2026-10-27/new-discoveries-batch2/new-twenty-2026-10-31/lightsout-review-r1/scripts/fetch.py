import os,resource,sys,urllib.request,json,hashlib,datetime
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
r=Path(__file__).resolve().parents[1];(r/'sources').mkdir(exist_ok=True)
name,url=sys.argv[1:]; rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-review/1.0'}),timeout=25) as f:
  d=f.read();rec.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(d).hexdigest(),bytes=len(d));(r/'sources'/name).write_bytes(d)
except Exception as e:rec['error']=str(e)
(r/'receipts'/(name+'.json')).write_text(json.dumps(rec,indent=2));print(json.dumps(rec))
