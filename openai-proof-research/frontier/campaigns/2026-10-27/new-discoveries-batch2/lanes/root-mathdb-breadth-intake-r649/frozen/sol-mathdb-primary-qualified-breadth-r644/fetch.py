import pathlib,json,urllib.request,hashlib,datetime,subprocess,re
from html.parser import HTMLParser
P=pathlib.Path(__file__).resolve().parent
log=[]
def get(url,name):
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'ResearchReader/1.0'}),timeout=25) as r:b=r.read();final=r.url
  (P/name).write_bytes(b);log.append(dict(url=url,final_url=final,path=name,size=len(b),sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='bound_before_inspection'));(P/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n');return b
 except Exception as e:
  log.append(dict(url=url,error=str(e),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),retry=False));(P/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n');return None
class Links(HTMLParser):
 def __init__(self):super().__init__();self.urls=[]
 def handle_starttag(self,t,a):
  for k,v in a:
   if k in ['href','content'] and v and '.pdf' in v:self.urls.append(v)
for id in [1532,1537,1587,1593]:
 b=get('https://ems.press/journals/owr/articles/'+str(id),'ems'+str(id)+'.html')
 if b is None:continue
 h=Links();h.feed(b.decode());urls=list(dict.fromkeys(h.urls));print(id,urls)
 if not urls:continue
 url=urllib.request.urljoin('https://ems.press',urls[0]);name='ems'+str(id)+'.pdf';b=get(url,name)
 if b is None:continue
 subprocess.run(['pdftotext','-layout',str(P/name),str(P/name.replace('.pdf','.txt'))],check=True)
 t=P/name.replace('.pdf','.txt');b=t.read_bytes();log.append(dict(path=t.name,size=len(b),sha256=hashlib.sha256(b).hexdigest(),derived_from=name,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='bound_before_reading'));(P/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
