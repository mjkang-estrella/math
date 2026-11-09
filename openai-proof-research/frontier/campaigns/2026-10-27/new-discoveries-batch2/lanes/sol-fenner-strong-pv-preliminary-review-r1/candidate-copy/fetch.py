import os,resource
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(30,30))
import urllib.request,json,datetime,hashlib,sys
from pathlib import Path
from html.parser import HTMLParser
b=Path(__file__).resolve().parent
class T(HTMLParser):
 def __init__(self):super().__init__();self.a=[]
 def handle_data(self,s):self.a.append(s)
def get(n,u):
 r={'file':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'bounded-math-research'}),timeout=20) as f:
   d=f.read(20000000);r.update(status=f.status,bytes=len(d),sha256=hashlib.sha256(d).hexdigest());(b/'sources'/n).write_bytes(d)
  if n.endswith('.html'):
   t=T();t.feed(d.decode());(b/'sources'/n.replace('.html','.txt')).write_text('\n'.join(t.a))
 except Exception as e:r['error']=str(e)
 p=b/'http.json';a=json.loads(p.read_text()) if p.exists() else [];a.append(r);p.write_text(json.dumps(a,indent=2));print(r)
if __name__=='__main__':get(*sys.argv[1:])
