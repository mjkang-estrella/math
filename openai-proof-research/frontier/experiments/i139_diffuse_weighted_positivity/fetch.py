from pathlib import Path
import urllib.request,json,hashlib
from html.parser import HTMLParser
S=Path('frontier/sources/i139_diffuse_weighted_positivity/primary');S.mkdir(exist_ok=True)
class Extract(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ('script','style'):self.skip+=1
  if t in ('p','div','section','h1','h2','h3','h4','li','table','tr'):self.out.append('\n')
 def handle_endtag(self,t):
  if t in ('script','style'):self.skip-=1
  if t in ('p','div','section','h1','h2','h3','h4','li','tr'):self.out.append('\n')
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
def extract(b):
 p=Extract();p.feed(b.decode());ls=[' '.join(l.split()) for l in ''.join(p.out).splitlines()];return ('\n'.join(l for l in ls if l)+'\n').encode()
rows=[]
for name,url in [('roe-abs','https://arxiv.org/abs/0804.1662'),('roe-v1','https://arxiv.org/html/0804.1662v1'),('dumnicki-abs','https://arxiv.org/abs/math/0606716'),('dumnicki-v1','https://arxiv.org/html/math/0606716v1'),('evans-abs','https://arxiv.org/abs/2605.27574'),('evans-v2','https://arxiv.org/html/2605.27574v2'),('ito-abs','https://arxiv.org/abs/1202.6662')]:
 rec=dict(name=name,url=url)
 try:
  with urllib.request.urlopen(url,timeout=40) as r:b=r.read();rec.update(status=r.status,final_url=r.url)
  (S/(name+'.html')).write_bytes(b);t=extract(b);(S/(name+'.txt')).write_bytes(t);rec.update(sha256=hashlib.sha256(b).hexdigest(),lines=len(t.decode().splitlines()))
 except Exception as e:rec['failure']=str(e)
 rows.append(rec); print(rec,flush=True)
(S/'retrievals.json').write_text(json.dumps(rows,indent=2)+'\n')
