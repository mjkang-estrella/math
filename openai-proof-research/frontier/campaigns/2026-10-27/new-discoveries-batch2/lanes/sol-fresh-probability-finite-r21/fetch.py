import urllib.request,urllib.error,json,datetime,hashlib,pathlib,resource,concurrent.futures
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(45,45))
b=pathlib.Path(__file__).resolve().parent
jobs=[('probability.json','https://mathdb.com/api/posts?tag=probability&limit=100'),('combinatorics.json','https://mathdb.com/api/posts?tag=combinatorics&limit=100')]+[(n+'-head.json','https://api.github.com/repos/'+r+'/commits/HEAD') for n,r in [('omega','the-omega-institute/trureturing'),('openai','openai/math'),('count','suvrit/count-ex-machina')]]
def fetch(job):
 n,u=job;r={'file':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=25) as f:d=f.read(20000000);r['status']=f.status
  (b/'sources'/n).write_bytes(d);r.update(sha256=hashlib.sha256(d).hexdigest(),bytes=len(d))
 except Exception as e:r['error']=str(e)
 return r
receipts=list(concurrent.futures.ThreadPoolExecutor(5).map(fetch,jobs))
(b/'http.json').write_text(json.dumps(receipts,indent=2));print(json.dumps(receipts,indent=2))
