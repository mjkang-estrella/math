"""Acquisition only; never imported by offline replay."""
import json,hashlib,urllib.request,pathlib,datetime,sys
from html.parser import HTMLParser
class View(HTMLParser):
 def __init__(self):super().__init__(convert_charrefs=True);self.parts=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ("script","style"):self.skip+=1
 def handle_endtag(self,t):
  if t in ("script","style"):self.skip=max(0,self.skip-1)
 def handle_data(self,d):
  if not self.skip and d.strip():self.parts.append(d.strip())
S=pathlib.Path('frontier/sources/i132_discrete_probability_discovery');(S/'external').mkdir(exist_ok=True)
log=json.loads((S/'http-log.json').read_text()) if (S/'http-log.json').exists() else []
for name,url in [tuple(x.split('=',1)) for x in sys.argv[1:]]:
 r={'name':name,'url':url,'at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0 research evidence'}),timeout=45) as f: data=f.read();r.update(status=f.status,final_url=f.url,content_type=f.headers.get('Content-Type'))
  p=S/'external'/name;p.write_bytes(data);r.update(path=str(p),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  if not name.endswith('.pdf'):
   parser=View();parser.feed(data.decode('utf-8'));view='\n'.join(parser.parts);v=p.with_suffix('.txt');v.write_text(view);r.update(view=str(v),view_sha256=hashlib.sha256(view.encode()).hexdigest(),view_convention='stdlib HTMLParser convert_charrefs; exclude script/style; stripped nonempty text nodes LF joined; no final LF')
 except Exception as e:r['error']=repr(e)
 log.append(r);(S/'http-log.json').write_text(json.dumps(log,indent=2)+'\n');print(json.dumps(r))
