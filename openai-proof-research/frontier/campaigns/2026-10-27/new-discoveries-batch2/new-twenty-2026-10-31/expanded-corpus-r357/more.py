exec(compile(open('investigate.py').read().split("mode=sys.argv[1]")[0],'caps','exec'))
from concurrent.futures import ThreadPoolExecutor
jobs=[('1606.06248.pdf','https://arxiv.org/pdf/1606.06248'),('1610.05290.pdf','https://arxiv.org/pdf/1610.05290'),('1610.09587.pdf','https://arxiv.org/pdf/1610.09587'),('1606.04029.pdf','https://arxiv.org/pdf/1606.04029'),('2611.01172.pdf','https://arxiv.org/pdf/2611.01172')]
def fetch(t):
 n,u=t;rec={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'GET'}
 try:
  with urllib.request.urlopen(u,timeout=12) as q:
   b=q.read(16000001);assert len(b)<=16000000;put('sources/'+n,b);rec.update(status=q.status,final_url=q.url,bytes=len(b),sha256=sha(b))
 except Exception as e:rec.update(error=repr(e),status=getattr(e,'code',None))
 js('http/'+n+'.json',rec);return rec
with ThreadPoolExecutor(max_workers=2) as pool:r=list(pool.map(fetch,jobs))
print(json.dumps(r));receipt('more',{'true_exit':0,'threads':2,'joined':True})
