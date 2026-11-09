import urllib.request,json,hashlib,datetime,resource,concurrent.futures,subprocess
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
base=Path(__file__).parent; (base/'sources').mkdir(exist_ok=True)
urls={
'original-abs':'https://arxiv.org/abs/math/0607326',
'journal':'https://link.springer.com/content/pdf/10.1007/s10711-008-9307-4.pdf',
'span-abs':'https://arxiv.org/abs/2504.00834',
'span-v1':'https://arxiv.org/pdf/2504.00834v1',
'span-v2':'https://arxiv.org/pdf/2504.00834v2',
'patterns':'https://arxiv.org/pdf/1801.01225',
'broken':'https://arxiv.org/pdf/1911.13226',
'A2':'https://arxiv.org/pdf/1609.03585',
'openai-head':'https://github.com/openai/math',
'openai-contents':'https://raw.githubusercontent.com/openai/math/HEAD/CONTENTS.md',
'leanpool':'https://raw.githubusercontent.com/Vilin97/lean-pool/HEAD/LeanPool/projects.yml'
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
(base/'fetch-receipts.json').write_text(json.dumps(results,indent=2));print(json.dumps(results,indent=2))
