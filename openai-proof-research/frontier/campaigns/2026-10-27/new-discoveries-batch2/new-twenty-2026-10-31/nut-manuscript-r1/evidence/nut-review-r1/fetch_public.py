import pathlib,urllib.request,urllib.error,hashlib,json,datetime,resource,os
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=pathlib.Path(__file__).resolve().parent/'public';p.mkdir(exist_ok=True)
urls={'openai-head.json':'https://api.github.com/repos/openai/math/commits/HEAD','omega-head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','frustration.html':'https://arxiv.org/html/2610.15679v1','degrees.html':'https://arxiv.org/html/2410.14063v3','quartic.html':'https://arxiv.org/html/2502.06353v2','vertex.html':'https://dmtcs.episciences.org/17258/pdf'}
r={}
for n,u in urls.items():
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'MathDB independent review (public research)'}),timeout=18) as x:data=x.read();status=x.status
  (p/n).write_bytes(data);r[n]={'url':u,'status':status,'sha256':hashlib.sha256(data).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  if n.endswith('.json'):
   d=json.loads(data);r[n].update(head=d['sha'],message=d['commit']['message'],date=d['commit']['committer']['date'],files=[f['filename'] for f in d.get('files',[])])
 except Exception as e:r[n]={'url':u,'error':str(e),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'retried':False}
(p/'receipts.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
