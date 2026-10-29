import resource,signal,os
resource.setrlimit(resource.RLIMIT_AS,(536870912,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,20));signal.alarm(55)
import urllib.request,hashlib,json,datetime
from pathlib import Path
from html.parser import HTMLParser
b=Path(__file__).parent; log=[]
class Text(HTMLParser):
 def __init__(self):super().__init__();self.a=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['p','section','h1','h2','h3','h4','h5','h6','li']:self.a.append('\n')
 def handle_data(self,d):self.a.append(d)
for name,url in [('new-law','https://arxiv.org/html/2610.00101v1'),('new-law-abs','https://arxiv.org/abs/2610.00101'),('companion','https://arxiv.org/html/2608.30254v2'),('target-abs','https://arxiv.org/abs/2608.28007'),('clopen','https://clopen.solutions/?q=weighted+selection')]:
 try:
  with urllib.request.urlopen(url,timeout=9) as r:z=r.read(12000000);status=r.status
  (b/'sources'/f'{name}.html').write_bytes(z);p=Text();p.feed(z.decode());(b/'sources'/f'{name}.txt').write_text(''.join(p.a));log.append(dict(url=url,file=f'sources/{name}.html',status=status,sha256=hashlib.sha256(z).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 except Exception as e:
  log.append(dict(url=url,error=str(e),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
  if getattr(e,'code',None) in [403,429]:break
 (b/'http-log.json').write_text(json.dumps(log,indent=2))
print(json.dumps(log,indent=2))
