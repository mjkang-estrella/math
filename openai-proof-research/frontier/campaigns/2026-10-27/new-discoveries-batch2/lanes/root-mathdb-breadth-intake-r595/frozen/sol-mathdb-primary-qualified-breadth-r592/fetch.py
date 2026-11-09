import pathlib,json,urllib.request,datetime,hashlib
from html.parser import HTMLParser
P=pathlib.Path(__file__).resolve().parent
class Extract(HTMLParser):
 def __init__(self):super().__init__();self.s=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip=max(0,self.skip-1)
 def handle_data(self,d):
  if not self.skip and d.strip():self.s.append(d.strip())
def bind(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
prov=[];fails=[]
for name,url in [('matroid-primary','https://ems.press/content/serial-article-files/46772'),('matroid-successor','https://pmc.ncbi.nlm.nih.gov/articles/PMC9237001/'),('utb-primary','https://ems.press/journals/owr/articles/15430'),('mixed-primary','https://ems.press/journals/owr/articles/15587')]:
 utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read();ct=r.headers.get('Content-Type','');final=r.url
  p=P/(name+'.html');p.write_bytes(b);e=bind(p);e.update(url=url,final_url=final,utc=utc,content_type=ct);prov.append(e)
  (P/'source-provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
  if b.startswith(b'%PDF'):fails.append(dict(url=url,failure='PDF bytes saved under html suffix; no extraction attempted'));continue
  x=Extract();x.feed(b.decode('utf-8',errors='replace'));t=P/(name+'.txt');t.write_text('\n'.join(x.s));der=bind(t);der.update(parent_sha256=e['sha256'],url=url,utc=utc);prov.append(der)
  (P/'source-provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
 except Exception as e:fails.append(dict(url=url,utc=utc,failure=str(e)))
(P/'fetch-failures.json').write_text(json.dumps(fails,indent=2)+'\n')
print(json.dumps(prov));print('failures',fails)
