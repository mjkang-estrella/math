import resource,signal,urllib.request,datetime,hashlib,json
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,20));signal.alarm(55)
b=Path(__file__).parent;log=[]
for name,url in [('li-current-abs.html','https://arxiv.org/abs/2609.03653'),('pick.html','https://arxiv.org/html/1804.03931v1'),('clopen-current.html','https://clopen.solutions/')]:
 r={'url':url,'utc_started':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'public-math-research/1.0'}),timeout=14) as f:data=f.read(12000000);r['status']=f.status
  (b/'sources'/name).write_bytes(data);r['sha256']=hashlib.sha256(data).hexdigest()
 except Exception as e:r['error']=str(e)
 r['utc_finished']=datetime.datetime.now(datetime.timezone.utc).isoformat();log.append(r)
 (b/'http-log.json').write_text(json.dumps(log,indent=2))
print(json.dumps(log,indent=2))
