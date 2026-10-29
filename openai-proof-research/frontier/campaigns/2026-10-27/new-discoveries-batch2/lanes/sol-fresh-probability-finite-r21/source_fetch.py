import urllib.request,urllib.error,json,datetime,hashlib,pathlib,resource,concurrent.futures
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(45,45))
b=pathlib.Path(__file__).resolve().parent
jobs=[('omega-Blueprint-tree.json', 'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/94b17928f1da59dddf371355b5d596be3d07dd5b?recursive=1'), ('omega-D5-tree.json', 'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/e39e83d6bffebcbc1755049907a3c79069ae4983?recursive=1'), ('omega-Problems-tree.json', 'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/9f3d2d75496a0bc539877cf4aa5a07ccd7a20712?recursive=1'), ('brugidou.html', 'https://arxiv.org/html/2306.15300v3')]
def fetch(job):
 n,u=job;r={'file':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=25) as f:d=f.read(20000000);r['status']=f.status
  (b/'sources'/n).write_bytes(d);r.update(sha256=hashlib.sha256(d).hexdigest(),bytes=len(d))
 except Exception as e:r['error']=str(e)
 return r
receipts=list(concurrent.futures.ThreadPoolExecutor(5).map(fetch,jobs))
(b/'http-source.json').write_text(json.dumps(receipts,indent=2));print(json.dumps(receipts,indent=2))
