from pathlib import Path
import urllib.request,json,datetime,hashlib
from html.parser import HTMLParser
P=Path(__file__).resolve().parent
class Text(HTMLParser):
 def __init__(self): super().__init__();self.s=[]
 def handle_data(self,d): self.s.append(d)
a=json.load(open(P/'retrievals.json'))
for name,url in [('miyamoto-abs.html','https://arxiv.org/abs/2402.06618'),('companion-v2.html','https://arxiv.org/html/2404.11455v2'),('mathdb.html','https://mathdb.com/p/361811')]:
 try:
  r=urllib.request.urlopen(url,timeout=30);b=r.read();(P/'sources'/name).write_bytes(b);d={'file':name,'url':url,'status':r.status,'sha256':hashlib.sha256(b).hexdigest(),'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 except Exception as e:d={'file':name,'url':url,'error':str(e),'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 a.append(d);print(d)
(P/'retrievals.json').write_text(json.dumps(a,indent=2))
for p in (P/'sources').glob('*.html'):
 t=Text();t.feed(p.read_text());p.with_suffix('.txt').write_text('\n'.join(t.s))
