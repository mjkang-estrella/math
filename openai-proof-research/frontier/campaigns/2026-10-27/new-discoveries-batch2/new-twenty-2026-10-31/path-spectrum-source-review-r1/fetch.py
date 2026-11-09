import pathlib,urllib.request,urllib.error,json,hashlib,datetime,resource,signal,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));signal.alarm(140)
p=pathlib.Path(__file__).resolve().parent
jobs=[('journal-article.html','https://www.sciencedirect.com/science/article/pii/S0012365X25003292'),('matzke-research.html','https://www.ryanmatzke.com/research'),('crossref.json','https://api.crossref.org/works/10.1016/j.disc.2025.114721'),('openalex.json','https://api.openalex.org/works/https://doi.org/10.1016/j.disc.2025.114721'),('arxiv-current.html','https://arxiv.org/abs/2409.04869')]
for name,url in jobs:
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'SourceReview/1.0'}),timeout=16) as f:b=f.read(12000000);r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
 except urllib.error.HTTPError as e:b=e.read();r.update(status=e.code,error=str(e))
 except Exception as e:b=b'';r.update(error=repr(e))
 (p/name).write_bytes(b);r.update(path=str(p/name),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));
 with (p/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(name,r.get('status'),r.get('error'),len(b),flush=True)
