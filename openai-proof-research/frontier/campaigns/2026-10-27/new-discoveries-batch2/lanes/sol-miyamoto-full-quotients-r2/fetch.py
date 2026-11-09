import os,resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(25,25))
for k in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
from pathlib import Path
import urllib.request,datetime,hashlib,json
b=Path(__file__).resolve().parent;(b/'sources').mkdir(exist_ok=True)
urls={'target.html':'https://arxiv.org/html/2402.06618v2','companion.html':'https://arxiv.org/html/2404.11455v2','followup.html':'https://arxiv.org/html/2602.10992v1','author.html':'https://roland.miyamoto.casa/','count-registry-current.json':'https://raw.githubusercontent.com/suvrit/count-ex-machina/main/registry.json'}
r=[]
for fn,url in urls.items():
 v={'url':url,'file':'sources/'+fn,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=20) as h:data=h.read();v['status']=h.status;v['headers']=dict(h.headers)
  (b/'sources'/fn).write_bytes(data);v.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 except Exception as e:v['error']=str(e)
 r.append(v)
(b/'retrievals.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
