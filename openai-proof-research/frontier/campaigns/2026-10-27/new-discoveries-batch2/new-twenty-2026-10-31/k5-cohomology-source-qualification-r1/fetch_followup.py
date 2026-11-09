import urllib.request,json,hashlib,datetime,resource,concurrent.futures,subprocess
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
base=Path(__file__).parent; (base/'sources').mkdir(exist_ok=True)
urls={
'mathdb-live':'https://mathdb.com/p/379886/cohomology-conjecture-for-the-complete-graph-k-5',
'leanpool-head':'https://github.com/Vilin97/lean-pool',
'openai-pinned-contents':'https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/CONTENTS.md',
'journal-article':'https://link.springer.com/article/10.1007/s10711-008-9307-4',
'patterns-abs':'https://arxiv.org/abs/1801.01225',
'broken-abs':'https://arxiv.org/abs/1911.13226'
}

def get(k,u):
 r={'key':k,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=22) as q:
   d=q.read(16000001);r.update(status=q.status,final_url=q.url,bytes=len(d),sha256=hashlib.sha256(d).hexdigest())
   (base/'sources'/k).write_bytes(d)
  if d.startswith(b'%PDF'): subprocess.run(['pdftotext','-layout',str(base/'sources'/k),str(base/'sources'/(k+'.txt'))],timeout=15,check=True)
 except Exception as e:r['error']=str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex: results=list(ex.map(lambda x:get(*x),urls.items()))
(base/'followup-fetch-receipts.json').write_text(json.dumps(results,indent=2));print(json.dumps(results,indent=2))
