import pathlib,urllib.request,hashlib,json,datetime,concurrent.futures,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
L=pathlib.Path(__file__).resolve().parent;(L/'sources').mkdir(exist_ok=True)
urls={'registry-openai':'https://api.github.com/repos/OpenAI/math/commits/HEAD','registry-omega':'https://api.github.com/repos/teorth/analysis/commits/HEAD','2008.11448':'https://arxiv.org/pdf/2008.11448','2009.04510':'https://arxiv.org/pdf/2009.04510','2010.05521':'https://arxiv.org/pdf/2010.05521','2010.01655':'https://arxiv.org/pdf/2010.01655'}
def fetch(k,u):
 r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Math research source fidelity'}),timeout=35) as x:
   b=x.read(20000000);r.update(status=x.status,final_url=x.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(L/'sources'/k).write_bytes(b)
 except Exception as e:r['error']=str(e)
 return k,r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as e:r=dict(e.map(lambda z:fetch(*z),urls.items()))
(L/'source-receipts.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
