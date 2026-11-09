import pathlib,urllib.request,json,hashlib,datetime
from html.parser import HTMLParser
P=pathlib.Path(__file__).resolve().parent
out=[];fails=[]
for id in ['12861','14741','12975','12872','12983']:
 url='https://ems.press/journals/owr/articles/'+id; now=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read();final=r.url
  p=P/('ems-'+id+'.html');p.write_bytes(b)
  out.append(dict(path=p.name,url=url,final_url=final,utc=now,size=len(b),sha256=hashlib.sha256(b).hexdigest(),version='served HTML at retrieval UTC'))
 except Exception as e:fails.append(dict(url=url,utc=now,error=str(e)))
(P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');(P/'fetch-failures.json').write_text(json.dumps(fails,indent=2)+'\n')
# Bind raw bytes before parsing. Persist derivative bindings before any content display.
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,s):self.parts.append(s)
derived=[]
for e in out:
 b=(P/e['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==e['sha256']
 h=Parser();h.feed(b.decode());p=P/e['path'].replace('.html','.txt');p.write_text('\n'.join(h.parts));b=p.read_bytes()
 derived.append(dict(path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest(),from_path=e['path'],method='stdlib HTMLParser handle_data; includes navigation/scripts'))
(P/'derivative-bindings.json').write_text(json.dumps(derived,indent=2)+'\n')
print(json.dumps(out+fails,indent=2))
