import urllib.request,hashlib,json,pathlib,datetime,html.parser
O=pathlib.Path(__file__).resolve().parent
class Parser(html.parser.HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.links=[]
 def handle_data(self,d):self.parts.append(d)
 def handle_starttag(self,t,a):
  for k,v in a:
   if k in ('href','content') and v and ('.pdf' in v or 'arxiv' in v):self.links.append(v)
pro=[];fail=[]
for name,url in [('rectangle','https://ems.press/journals/owr/articles/4416'),('invariants','https://ems.press/journals/owr/articles/4797'),('approximation','https://ems.press/journals/owr/articles/11791'),('inversion','https://ems.press/journals/owr/articles/4807')]:
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read();final=f.url
  p=O/(name+'.html');p.write_bytes(b);pro.append(dict(path=str(p),url=url,final_url=final,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
 except Exception as e:fail.append(dict(url=url,error=str(e),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
(O/'source-provenance.json').write_text(json.dumps(pro,indent=2)+'\n');(O/'fetch-failures.json').write_text(json.dumps(fail,indent=2)+'\n')
der=[]
for r in pro:
 p=pathlib.Path(r['path']);h=Parser();h.feed(p.read_text());q=p.with_suffix('.txt');q.write_text('\n'.join(h.parts));der.append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),size=q.stat().st_size));print(p.name,h.links)
(O/'derivative-bindings.json').write_text(json.dumps(der,indent=2)+'\n')
print('FAILURES',fail)
