import pathlib,urllib.request,json,hashlib,datetime,resource,os
resource.setrlimit(resource.RLIMIT_CPU,(120,120));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=pathlib.Path(__file__).resolve().parent/'public';r={}
for name,url in [('metadata-companion.html','https://arxiv.org/abs/1808.08747'),('degrees-v1.html','https://arxiv.org/html/2410.14063v1'),('quartic-v1.html','https://arxiv.org/html/2502.06353v1')]:
 try:
  with urllib.request.urlopen(url,timeout=18) as x:d=x.read();status=x.status
  (p/name).write_bytes(d);r[name]={'url':url,'status':status,'sha256':hashlib.sha256(d).hexdigest()}
 except Exception as e:r[name]={'url':url,'error':str(e),'retried':False}
 r[name]['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
(p/'more-receipts.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
