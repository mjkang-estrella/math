"""Preparation only; current primary records, owned paths, no inherited reruns."""
from pathlib import Path
from html.parser import HTMLParser
import urllib.request,json,hashlib,datetime
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i142_uniform_algebraic_allocation'; P=S/'primary';P.mkdir(exist_ok=True)
assert not (S/'seal.json').exists()
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
urls={'ito-abs':'https://arxiv.org/abs/1202.6662','roe-abs':'https://arxiv.org/abs/0804.1662','dumnicki-abs':'https://arxiv.org/abs/math/0606716','evans-abs':'https://arxiv.org/abs/2605.27574','biran-abs':'https://arxiv.org/abs/alg-geom/9705018','biran-v2':'https://arxiv.org/html/alg-geom/9705018v2'}
records=[]
for name,url in urls.items():
 rec=dict(name=name,url=url,retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  b=urllib.request.urlopen(url,timeout=45).read();(P/(name+'.html')).write_bytes(b)
  p=Extract();p.feed(b.decode());ls=[' '.join(l.split()) for l in ''.join(p.out).splitlines()];t='\n'.join(l for l in ls if l)+'\n';(P/(name+'.txt')).write_text(t)
  rec.update(sha256=hashlib.sha256(b).hexdigest(),lines=len(t.splitlines()))
 except Exception as e:rec['failure']=repr(e)
 records.append(rec)
(P/'retrievals.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(records,indent=2))
