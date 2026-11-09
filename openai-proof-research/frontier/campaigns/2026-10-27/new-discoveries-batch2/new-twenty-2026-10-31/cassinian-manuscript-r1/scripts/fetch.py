import urllib.request,urllib.error,json,hashlib,datetime,os,resource
from pathlib import Path
D=Path(__file__).resolve().parents[1]/'sources';D.mkdir(exist_ok=True)
os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]));resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
items=json.loads(__import__('sys').argv[1])
for n,u in items:
 r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'retries':0}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Math literature review (public academic sources)'}),timeout=12) as x:
   b=x.read(18000000);r.update(status=x.status,final_url=x.url,content_type=x.headers.get('Content-Type'));(D/n).write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 (D/(n+'.receipt.json')).write_text(json.dumps(r,indent=2)+'\n');print(n,r.get('status'),r.get('error',''))
