import os,resource,signal,requests,hashlib,json,datetime,sys
from pathlib import Path
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
resource.setrlimit(resource.RLIMIT_CPU,(45,45)); signal.alarm(55)
p=Path(__file__).resolve().parent
log=json.loads((p/'access.json').read_text()) if (p/'access.json').exists() else []
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':name}
 try:
  s=requests.get(url,timeout=15); data=s.content; (p/name).write_bytes(data)
  r.update(status=s.status_code,final_url=s.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),content_type=s.headers.get('Content-Type'))
 except Exception as e:r['error']=str(e)
 log.append(r); (p/'access.json').write_text(json.dumps(log,indent=2)); print(r)
