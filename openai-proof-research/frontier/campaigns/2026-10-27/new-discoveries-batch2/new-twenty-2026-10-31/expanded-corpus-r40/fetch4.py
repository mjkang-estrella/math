import pathlib,urllib.request,hashlib,json,datetime,concurrent.futures,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
L=pathlib.Path(__file__).resolve().parent;(L/'sources').mkdir(exist_ok=True)
urls={'omega-library-current':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/7327fcf9a7e910c7f7bac0b2a7ed0aac9e3cc02d?recursive=1','omega-problems-current':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/6829b90377cf0d5712a42527812611550884d6ba?recursive=1'}
def fetch(k,u):
 r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Math research source fidelity'}),timeout=35) as x:
   b=x.read(20000000);r.update(status=x.status,final_url=x.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(L/'sources'/k).write_bytes(b)
 except Exception as e:r['error']=str(e)
 return k,r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as e:r=dict(e.map(lambda z:fetch(*z),urls.items()))
(L/'source-receipts-4.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
